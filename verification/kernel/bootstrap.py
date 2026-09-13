#!/usr/bin/env python3
"""GPL-2.0-or-later. Install pinned proof tools locally; never run during proof checking."""
from __future__ import annotations

import hashlib
import json
import os
import platform
import stat
import subprocess
import sys
import tarfile
import urllib.request
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[2]
PIN = json.loads((Path(__file__).parent / "toolchain.json").read_text())


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def paths() -> tuple[Path, Path, Path]:
    key = platform.system() + "-" + platform.machine()
    if key not in PIN["lean"]["assets"]:
        raise RuntimeError("Unsupported local proof-tool platform: " + key)
    name = PIN["lean"]["assets"][key]["name"]
    base = ROOT / ".cache/proof-tools"
    return base / name.removesuffix(".tar.zst"), ROOT / ".cache/mathlib", base / name


def proof_environment(lean_root: Path) -> dict[str, str]:
    env = os.environ.copy()
    for key in ["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS", "LEAN_SYSROOT", "LEAN_LIB_PREFIX",
                "ELAN_TOOLCHAIN", "LAKE_HOME", "PYTHONOPTIMIZE"]:
        env.pop(key, None)
    env["PATH"] = str(lean_root / "bin") + os.pathsep + env.get("PATH", "")
    env["MATHLIB_CACHE_DIR"] = str(ROOT / ".cache/mathlib-downloads")
    return env


def installation_integrity(lean_root: Path, archive: Path) -> dict:
    """Compare installed release entries to the pinned archive, without extracting.

    This checks release file contents and link targets. It is not OS attestation
    and does not prevent another process changing a file after it was checked.
    """
    import zstandard

    asset = PIN["lean"]["assets"][platform.system() + "-" + platform.machine()]
    actual_archive = sha256(archive)
    if actual_archive != asset["sha256"]:
        raise RuntimeError("Lean release archive checksum mismatch")
    manifest, entries, hardlinks = [], {}, []
    with archive.open("rb") as src, zstandard.ZstdDecompressor().stream_reader(src) as stream:
        with tarfile.open(fileobj=stream, mode="r|") as tar:
            for member in tar:
                name = PurePosixPath(member.name)
                if name.is_absolute() or ".." in name.parts or not name.parts or name.parts[0] != lean_root.name:
                    raise RuntimeError("Unexpected release archive path: " + member.name)
                relative = PurePosixPath(*name.parts[1:])
                key = relative.as_posix()
                if key in entries:
                    raise RuntimeError("Duplicate release entry: " + key)
                installed = lean_root.joinpath(*relative.parts)
                mode = installed.lstat().st_mode  # Never accept a symlink in place of a regular file.
                entry = {"path": key}
                if member.isdir():
                    if not stat.S_ISDIR(mode):
                        raise RuntimeError("Release directory mismatch: " + key)
                    entry["kind"] = "directory"
                elif member.isfile():
                    if not stat.S_ISREG(mode):
                        raise RuntimeError("Release file type mismatch: " + key)
                    payload = tar.extractfile(member)
                    if payload is None:
                        raise RuntimeError("Missing release payload: " + key)
                    expected = hashlib.sha256()
                    with payload:
                        for block in iter(lambda: payload.read(4 * 1024 * 1024), b""):
                            expected.update(block)
                    if installed.stat().st_size != member.size or sha256(installed) != expected.hexdigest():
                        raise RuntimeError("Installed Lean file checksum mismatch: " + key)
                    entry.update(kind="file", size=member.size, sha256=expected.hexdigest())
                elif member.issym():
                    if not stat.S_ISLNK(mode) or os.readlink(installed) != member.linkname:
                        raise RuntimeError("Installed Lean symlink mismatch: " + key)
                    entry.update(kind="symlink", target=member.linkname)
                elif member.islnk():
                    if not stat.S_ISREG(mode):
                        raise RuntimeError("Installed Lean hardlink type mismatch: " + key)
                    target = PurePosixPath(member.linkname)
                    if target.is_absolute() or ".." in target.parts or not target.parts or target.parts[0] != lean_root.name:
                        raise RuntimeError("Unexpected hardlink target: " + member.linkname)
                    entry.update(kind="hardlink", target=PurePosixPath(*target.parts[1:]).as_posix())
                    hardlinks.append((installed, entry))
                else:
                    raise RuntimeError("Unsupported release archive entry: " + key)
                entries[key] = entry
                manifest.append(entry)
    for installed, entry in hardlinks:
        target = entries.get(entry["target"])
        if target is None or target["kind"] != "file" or sha256(installed) != target["sha256"]:
            raise RuntimeError("Installed Lean hardlink content mismatch: " + entry["path"])
        entry["sha256"] = target["sha256"]
        entry["size"] = target["size"]
    # Added module files could shadow trusted core imports. Reject every extra
    # installed path too; mutable package caches belong outside this release.
    actual_paths = {"."}
    for directory, dirs, files in os.walk(lean_root, followlinks=False):
        for name in dirs + files:
            actual_paths.add((Path(directory) / name).relative_to(lean_root).as_posix())
    if actual_paths != set(entries):
        raise RuntimeError("Unexpected/missing installed Lean paths: " + repr(sorted(actual_paths ^ set(entries))[:10]))
    manifest.sort(key=lambda entry: entry["path"])
    encoded = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
    return {"archiveSHA256": actual_archive, "manifestSHA256": hashlib.sha256(encoded).hexdigest(),
            "entryCount": len(manifest), "regularFileCount": sum(e["kind"] == "file" for e in manifest),
            "symlinkCount": sum(e["kind"] == "symlink" for e in manifest), "entries": manifest,
            "limits": "Release contents/link targets verified at check time; OS, Python/zstandard, dynamic system libraries, and absence of concurrent mutation remain trusted."}


def check_pins(lean_root: Path, mathlib: Path) -> dict:
    lean_hash = subprocess.check_output([str(lean_root / "bin/lean"), "--githash"], text=True).strip()
    if lean_hash != PIN["lean"]["commit"]:
        raise RuntimeError("Unreviewed Lean binary version")
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
    if actual != PIN["mathlib"]["commit"]:
        raise RuntimeError("Unreviewed mathlib source revision")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=mathlib,
                   check=True, stdout=subprocess.DEVNULL)
    manifest = json.loads((mathlib / "lake-manifest.json").read_text())
    deps = {}
    for package in manifest["packages"]:
        folder = mathlib / manifest["packagesDir"] / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=folder, text=True).strip()
        if revision != package["rev"]:
            raise RuntimeError("Unreviewed mathlib dependency: " + package["name"])
        subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=folder,
                       check=True, stdout=subprocess.DEVNULL)
        deps[package["name"]] = revision
    return {"leanCommit": lean_hash, "mathlibCommit": actual, "dependencies": deps}


def main() -> None:
    if sys.version_info < (3, 12):
        raise RuntimeError("Proof-tool bootstrap requires Python 3.12+ for safe archive extraction")
    import zstandard

    lean_root, mathlib, archive = paths()
    asset = PIN["lean"]["assets"][platform.system() + "-" + platform.machine()]
    archive.parent.mkdir(parents=True, exist_ok=True)
    if not archive.exists():
        request = urllib.request.Request(PIN["lean"]["releaseBaseURL"] + asset["name"],
                                         headers={"User-Agent": "find-orb-verification"})
        pending = archive.with_suffix(archive.suffix + ".download")
        with urllib.request.urlopen(request, timeout=180) as response, pending.open("wb") as target:
            while block := response.read(4 * 1024 * 1024):
                target.write(block)
        if sha256(pending) != asset["sha256"]:
            raise RuntimeError("Lean download checksum mismatch")
        pending.replace(archive)
    if sha256(archive) != asset["sha256"]:
        raise RuntimeError("Cached Lean release checksum mismatch")
    if not (lean_root / "bin/lean").exists():
        with archive.open("rb") as src, zstandard.ZstdDecompressor().stream_reader(src) as stream:
            with tarfile.open(fileobj=stream, mode="r|") as tar:
                tar.extractall(archive.parent, filter="data")
    integrity = installation_integrity(lean_root, archive)
    if not mathlib.exists():
        mathlib.mkdir(parents=True)
        subprocess.run(["git", "init", str(mathlib)], check=True)
        subprocess.run(["git", "fetch", "--depth", "1", PIN["mathlib"]["repository"],
                        PIN["mathlib"]["commit"]], cwd=mathlib, check=True)
        subprocess.run(["git", "checkout", "--detach", "FETCH_HEAD"], cwd=mathlib, check=True)
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
    if actual != PIN["mathlib"]["commit"]:
        raise RuntimeError("Existing mathlib checkout differs from pinned revision")
    subprocess.run([str(lean_root / "bin/lake"), "exe", "cache", "get",
                    *PIN["mathlib"]["cacheModules"]], cwd=mathlib,
                   env=proof_environment(lean_root), check=True)
    print(json.dumps({**check_pins(lean_root, mathlib), "installationIntegrity": {
        key: value for key, value in integrity.items() if key != "entries"}}, indent=2))


if __name__ == "__main__":
    main()
