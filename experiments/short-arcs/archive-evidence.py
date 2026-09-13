#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""Archive immutable short-arc evidence using only the Python standard library.

Build:   python3 experiments/short-arcs/archive-evidence.py
Verify:  python3 experiments/short-arcs/archive-evidence.py --verify
Restore: python3 experiments/short-arcs/archive-evidence.py --extract NEW_DIRECTORY

--output DIR selects the archive/manifest directory (default results/short-arcs).
Build refuses existing outputs. Extraction requires a new or empty directory and
restores repository-relative paths beneath it. Original .json.gz files are stored
as decoded .json tar members and restored with gzip level 9, mtime=0, no filename.
Decoded bytes are exact; original gzip byte streams are deliberately not retained.
Consequently historical compressed-file hashes remain provenance of the original
run, and will not necessarily match restored gzip streams. Raw JSON hashes do.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import lzma
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import tarfile
import tempfile
from typing import BinaryIO, Iterator


ROOT = Path(__file__).resolve().parents[2]
LOCAL = PurePosixPath("results/local/short-arcs")
GROUPS = (
    "development-v2", "heldout-v2", "followup-v2", "tracklets-v3",
    "heldout-wasm-v2", "controls-v2", "identifiability-v1", "selection-v2-sources",
)
SOURCE_FILES = (
    "experiments/short-arcs/build.mjs",
    "experiments/short-arcs/controls.mjs",
    "experiments/short-arcs/identifiability.mjs",
    "experiments/short-arcs/methods.mjs",
    "experiments/short-arcs/patches.mjs",
    "experiments/short-arcs/predictive.mjs",
    "experiments/short-arcs/protocol.json",
    "experiments/short-arcs/run.mjs",
    "benchmark/cases.mjs",
)
CHUNK = 1024 * 1024
SHA_LENGTH = 64


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def safe_relative(value: str) -> PurePosixPath:
    require(isinstance(value, str) and bool(value), "Path must be a nonempty string")
    path = PurePosixPath(value)
    require(not path.is_absolute() and str(path) == value, f"Noncanonical relative path: {value}")
    require(all(part not in (".", "..", "") for part in path.parts), f"Unsafe path: {value}")
    require("\\" not in value and "\0" not in value and ":" not in path.parts[0], f"Unsafe path: {value}")
    return path


def digest(stream: BinaryIO) -> tuple[str, int]:
    value = hashlib.sha256()
    size = 0
    while block := stream.read(CHUNK):
        value.update(block)
        size += len(block)
    return value.hexdigest(), size


def file_digest(path: Path) -> tuple[str, int]:
    with path.open("rb") as source:
        return digest(source)


def decoded(path: Path, encoding: str) -> BinaryIO:
    return gzip.open(path, "rb") if encoding == "gzip" else path.open("rb")


def input_files() -> list[tuple[str, Path]]:
    result = []
    for group in GROUPS:
        directory = ROOT / LOCAL / group
        require(directory.is_dir() and not directory.is_symlink(), f"Missing or symlinked group: {directory}")
        entries = sorted(directory.rglob("*"))
        require(bool(entries), f"Empty result group: {group}")
        for path in entries:
            require(not path.is_symlink(), f"Symlink is not permitted: {path}")
            if path.is_dir():
                continue
            require(stat.S_ISREG(path.stat().st_mode), f"Nonregular file: {path}")
            relative = path.relative_to(ROOT / LOCAL).as_posix()
            result.append((relative[:-3] if relative.endswith(".json.gz") else relative, path))
    for relative in SOURCE_FILES:
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink(), f"Missing or symlinked source: {path}")
        result.append(("repository/" + relative, path))
    result.sort(key=lambda pair: pair[0])
    require(len({name for name, _ in result}) == len(result), "Decoded archive names collide")
    return result


def inventory() -> list[dict]:
    records = []
    for archive_path, path in input_files():
        encoding = "gzip" if path.name.endswith(".json.gz") else "identity"
        original_sha, original_size = file_digest(path)
        with decoded(path, encoding) as source:
            content_sha, content_size = digest(source)
        records.append({"archivePath": archive_path, "originalPath": path.relative_to(ROOT).as_posix(),
                        "encoding": encoding, "sha256": content_sha, "bytes": content_size,
                        "originalSha256": original_sha, "originalBytes": original_size})
    return records


def objects(value: object) -> Iterator[dict]:
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from objects(child)
    elif isinstance(value, list):
        for child in value:
            yield from objects(child)


def check_references(records: list[dict], documents: dict[str, object]) -> dict:
    """Check each published index reference against archived decoded-byte hashes.

    Compressed hashes refer to originalBytes/originalSha256, verified from actual
    compressed inputs during build. No claim is made that gzip re-encoding retains
    those compressed hashes. The tar members retain the complete decoded evidence.
    """
    by_original = {record["originalPath"]: record for record in records}
    referenced = set()
    raw_checks = 0
    original_gzip_checks = 0
    source_checks = 0

    def match(parent: PurePosixPath, filename: str, content_sha: str,
              compressed_sha: str | None = None) -> None:
        nonlocal raw_checks, original_gzip_checks
        target = (parent / safe_relative(filename)).as_posix()
        require(target in by_original, f"Referenced evidence is absent: {target}")
        record = by_original[target]
        require(record["encoding"] == "gzip", f"Raw evidence should be gzip: {target}")
        require(record["sha256"] == content_sha, f"Raw SHA256 mismatch: {target}")
        if compressed_sha is not None:
            require(record["originalSha256"] == compressed_sha, f"Original gzip SHA256 mismatch: {target}")
            original_gzip_checks += 1
        referenced.add(target)
        raw_checks += 1

    for name, document in documents.items():
        parent = safe_relative(name).parent
        for row in objects(document):
            if "rawSHA256" in row:
                filename = row.get("rawFile", row.get("filename"))
                require(isinstance(filename, str), f"Raw hash without filename in {name}")
                match(parent, filename, row["rawSHA256"], row.get("gzipSHA256"))
            if "uncompressedSHA256" in row:
                require(isinstance(row.get("file"), str), f"Raw hash without file in {name}")
                match(parent, row["file"], row["uncompressedSHA256"], row.get("compressedSHA256"))
        if name.endswith("/manifest.json") and isinstance(document, dict):
            if "plannedRuns" in document:
                require(bool(document.get("completedAt")), f"Run is incomplete: {name}")
                require(document.get("completedRuns") == document["plannedRuns"], f"Run count mismatch: {name}")
                result = documents[(parent / "results.json").as_posix()]
                require(isinstance(result, list) and len(result) == document["plannedRuns"], f"Index count mismatch: {name}")
            if "summarySHA256" in document:
                target = (parent / "summary.json").as_posix()
                require(by_original[target]["sha256"] == document["summarySHA256"], f"Summary hash mismatch: {name}")
            source_hashes = document.get("sourceSHA256")
            if isinstance(source_hashes, dict):
                for filename, expected in source_hashes.items():
                    target = (parent / "sources" / safe_relative(filename)).as_posix()
                    require(target in by_original and by_original[target]["sha256"] == expected,
                            f"Source snapshot hash mismatch: {target}")
                    source_checks += 1
        if name.endswith("/decision.json") and isinstance(document, dict):
            expected = document.get("developmentResultsSHA256")
            if expected:
                require(by_original[(parent / "results.json").as_posix()]["sha256"] == expected,
                        f"Frozen development index hash mismatch: {name}")
    all_raw = {row["originalPath"] for row in records if row["encoding"] == "gzip"}
    require(referenced == all_raw, "Unindexed raw evidence: " + ", ".join(sorted(all_raw - referenced)))

    # These source references hash file bytes (patchesSHA256 hashes an exported
    # object instead, so it is intentionally not mislabeled as a source-file hash).
    for group in GROUPS:
        key = (LOCAL / group / "manifest.json").as_posix()
        document = documents.get(key)
        if not isinstance(document, dict):
            continue
        source_candidates = {
            "methodsSHA256": [str(LOCAL / "selection-v2-sources/methods.mjs"), "experiments/short-arcs/methods.mjs"],
            "runnerSHA256": [str(LOCAL / "selection-v2-sources/run.mjs"), "experiments/short-arcs/run.mjs"],
            "predictiveSHA256": ["experiments/short-arcs/predictive.mjs"],
            "protocolSHA256": [str(LOCAL / "selection-v2-sources/protocol.json"), "experiments/short-arcs/protocol.json"],
            "commandBuilderSHA256": ["benchmark/cases.mjs"],
        }
        if group == "identifiability-v1":
            source_candidates["sourceSHA256"] = ["experiments/short-arcs/identifiability.mjs"]
            require(bool(documents[(LOCAL / group / "results.json").as_posix()].get("completedAt")),
                    "Identifiability result is incomplete")
        for field, candidates in source_candidates.items():
            if field in document:
                require(any(path in by_original and by_original[path]["sha256"] == document[field] for path in candidates),
                        f"No exact source for {group}/{field}")
                source_checks += 1
    return {"rawReferenceChecks": raw_checks, "distinctRawFiles": len(referenced),
            "originalGzipReferenceChecks": original_gzip_checks, "sourceReferenceChecks": source_checks}


def index_documents(records: list[dict]) -> dict[str, object]:
    return {row["originalPath"]: json.loads((ROOT / row["originalPath"]).read_bytes())
            for row in records if row["encoding"] == "identity" and row["originalPath"].endswith(".json")}


class HashReader:
    def __init__(self, source: BinaryIO):
        self.source = source
        self.hash = hashlib.sha256()
        self.size = 0

    def read(self, size: int = -1) -> bytes:
        value = self.source.read(size)
        self.hash.update(value)
        self.size += len(value)
        return value


def build(output: Path) -> None:
    output.mkdir(parents=True, exist_ok=True)
    archive = output / "evidence.tar.xz"
    manifest_path = output / "evidence-manifest.json"
    require(not archive.exists() and not manifest_path.exists(), "Build refuses existing archive or manifest")
    records = inventory()
    checks = check_references(records, index_documents(records))
    print(f"Verified {len(records)} inputs and {checks['rawReferenceChecks']} raw index references", flush=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=".evidence-", suffix=".tar.xz", dir=output)
    os.close(descriptor)
    temporary = Path(temporary_name)
    try:
        filters = [{"id": lzma.FILTER_LZMA2, "preset": 6, "dict_size": 16 * 1024 * 1024}]
        with lzma.open(temporary, "wb", format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64, filters=filters) as compressed:
            with tarfile.open(fileobj=compressed, mode="w|", format=tarfile.PAX_FORMAT) as tar:
                for index, record in enumerate(records):
                    path = ROOT / record["originalPath"]
                    info = tarfile.TarInfo(record["archivePath"])
                    info.size, info.mtime, info.mode = record["bytes"], 0, 0o644
                    info.uid = info.gid = 0
                    info.uname = info.gname = ""
                    with decoded(path, record["encoding"]) as source:
                        reader = HashReader(source)
                        tar.addfile(info, reader)
                        require(not reader.read(1), f"Input grew during build: {path}")
                        require(reader.hash.hexdigest() == record["sha256"] and reader.size == record["bytes"],
                                f"Input changed during build: {path}")
                    if (index + 1) % 250 == 0:
                        print(f"Packed {index + 1}/{len(records)} entries", flush=True)
        require([(name, path.relative_to(ROOT).as_posix()) for name, path in input_files()] ==
                [(row["archivePath"], row["originalPath"]) for row in records], "Input set changed during build")
        for record in records:
            require(file_digest(ROOT / record["originalPath"]) == (record["originalSha256"], record["originalBytes"]),
                    f"Original input changed during build: {record['originalPath']}")
        archive_sha, archive_size = file_digest(temporary)
        manifest = {"schemaVersion": 1, "archive": "evidence.tar.xz", "archiveSHA256": archive_sha,
                    "archiveBytes": archive_size, "entryCount": len(records),
                    "originalBytes": sum(row["originalBytes"] for row in records),
                    "decodedBytes": sum(row["bytes"] for row in records),
                    "groups": list(GROUPS), "compression": {"format": "xz", "lzma2Preset": 6, "dictionaryBytes": 16777216,
                    "check": "CRC64", "tar": "PAX, ordered regular files, mtime=uid=gid=0, mode=0644, empty owner names"},
                    "restoration": "Restore repository-relative originalPath beneath a new or empty --extract directory. Re-encode gzip entries using level 9, mtime 0 and no filename. Decoded bytes and rawSHA256 are exact; original gzip streams, headers and compressed-file hashes are not reproduced.",
                    "scope": "All files in the eight named experiment groups, plus exact small current experiment sources and the benchmark command builder. Independently pinned Horizons fixtures, upstream sources, binaries and ephemerides remain separate repository/release dependencies.",
                    "referenceVerification": checks, "files": records}
        # Exclusive destinations prevent accidental replacement, including during
        # another process's concurrent build. The temporary is local to output.
        with archive.open("xb") as destination, temporary.open("rb") as source:
            shutil.copyfileobj(source, destination, CHUNK)
        with manifest_path.open("x", encoding="utf-8") as destination:
            json.dump(manifest, destination, indent=2)
            destination.write("\n")
    finally:
        temporary.unlink(missing_ok=True)
    verify(output)


def load_manifest(output: Path) -> dict:
    manifest = json.loads((output / "evidence-manifest.json").read_bytes())
    require(manifest.get("schemaVersion") == 1 and manifest.get("archive") == "evidence.tar.xz", "Unsupported archive manifest")
    records = manifest["files"]
    require(isinstance(records, list) and len(records) == manifest["entryCount"], "Manifest count mismatch")
    require(manifest.get("groups") == list(GROUPS), "Unexpected evidence groups")
    names, originals = [], []
    for row in records:
        names.append(str(safe_relative(row["archivePath"])))
        originals.append(str(safe_relative(row["originalPath"])))
        require(row["encoding"] in ("gzip", "identity"), "Unknown entry encoding")
        original = PurePosixPath(row["originalPath"])
        if original.is_relative_to(LOCAL):
            relative = original.relative_to(LOCAL)
            require(relative.parts[0] in GROUPS, "Entry is outside the evidence groups")
            expected = str(relative)
            if row["encoding"] == "gzip":
                expected = expected[:-3]
        else:
            require(row["originalPath"] in SOURCE_FILES, "Unexpected repository source")
            expected = "repository/" + row["originalPath"]
        require(row["archivePath"] == expected, "Archive/original path mapping mismatch")
        require(isinstance(row["bytes"], int) and row["bytes"] >= 0, "Invalid entry size")
        require(isinstance(row["originalBytes"], int) and row["originalBytes"] >= 0, "Invalid original size")
        for key in ("sha256", "originalSha256"):
            value = row[key]
            require(isinstance(value, str) and len(value) == SHA_LENGTH and all(c in "0123456789abcdef" for c in value), "Invalid SHA256")
        require((row["encoding"] == "gzip") == row["originalPath"].endswith(".json.gz"), "Encoding/path mismatch")
        if row["encoding"] == "identity":
            require(row["sha256"] == row["originalSha256"] and row["bytes"] == row["originalBytes"],
                    "Identity entry changed bytes or size")
    require(names == sorted(names) and len(set(names)) == len(names), "Unordered or duplicate archive paths")
    require(len(set(originals)) == len(originals), "Duplicate original paths")
    require(sum(row["bytes"] for row in records) == manifest["decodedBytes"], "Decoded total mismatch")
    require(sum(row["originalBytes"] for row in records) == manifest["originalBytes"], "Original total mismatch")
    return manifest


def verify(output: Path) -> dict:
    manifest = load_manifest(output)
    archive = output / manifest["archive"]
    require(not archive.is_symlink(), "Symlinked archive is not accepted")
    require(file_digest(archive) == (manifest["archiveSHA256"], manifest["archiveBytes"]), "Archive SHA256/size mismatch")
    documents = {}
    with lzma.open(archive, "rb") as compressed:
        with tarfile.open(fileobj=compressed, mode="r|", ignore_zeros=True) as tar:
            for record in manifest["files"]:
                member = tar.next()
                require(member is not None and member.name == record["archivePath"], "Missing, extra or reordered tar entry")
                require(member.type == tarfile.REGTYPE and member.size == record["bytes"], "Tar type/size mismatch")
                require(member.mtime == 0 and member.uid == 0 and member.gid == 0 and member.mode == 0o644 and
                        member.uname == "" and member.gname == "", "Nonnormalized tar metadata")
                source = tar.extractfile(member)
                require(source is not None, "Unreadable tar entry")
                with source:
                    if record["encoding"] == "identity" and record["originalPath"].endswith(".json"):
                        content = source.read()
                        actual = (hashlib.sha256(content).hexdigest(), len(content))
                        documents[record["originalPath"]] = json.loads(content)
                    else:
                        actual = digest(source)
                require(actual == (record["sha256"], record["bytes"]), f"Decoded content mismatch: {member.name}")
            require(tar.next() is None, "Unexpected extra tar entry")
        # Reading the remaining compressed stream checks XZ trailers/checksums.
        while compressed.read(CHUNK):
            pass
    checks = check_references(manifest["files"], documents)
    require(checks == manifest["referenceVerification"], "Reference verification totals differ")
    print(f"Verified {manifest['entryCount']} entries, {manifest['archiveBytes']} archive bytes, SHA256 {manifest['archiveSHA256']}", flush=True)
    return manifest


def extract(output: Path, destination: Path) -> None:
    manifest = verify(output)  # Validate everything before writing any restored file.
    require(not destination.is_symlink(), "Extraction destination must not be a symlink")
    if destination.exists():
        require(destination.is_dir() and not any(destination.iterdir()), "Extraction requires a new or empty directory")
    else:
        destination.mkdir(parents=True)
    root = destination.resolve()
    by_name = {row["archivePath"]: row for row in manifest["files"]}
    with tarfile.open(output / manifest["archive"], "r|xz") as tar:
        for member in tar:
            record = by_name[member.name]
            target = root.joinpath(*safe_relative(record["originalPath"]).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            require(target.parent.resolve().is_relative_to(root), "Extraction parent escaped destination")
            require(not any(parent.is_symlink() for parent in target.parents if parent != root), "Symlinked extraction parent")
            source = tar.extractfile(member)
            require(source is not None, "Unreadable archive member")
            with source, target.open("xb") as output_file:
                if record["encoding"] == "gzip":
                    with gzip.GzipFile(filename="", mode="wb", compresslevel=9, fileobj=output_file, mtime=0) as encoded:
                        shutil.copyfileobj(source, encoded, CHUNK)
                else:
                    shutil.copyfileobj(source, output_file, CHUNK)
            with decoded(target, record["encoding"]) as restored:
                require(digest(restored) == (record["sha256"], record["bytes"]), "Restoration hash mismatch")
    print(f"Restored {len(manifest['files'])} files beneath {root}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    actions = parser.add_mutually_exclusive_group()
    actions.add_argument("--verify", action="store_true", help="Verify archive, every entry and original index references")
    actions.add_argument("--extract", type=Path, metavar="DIR", help="Restore beneath a new or empty directory")
    parser.add_argument("--output", type=Path, default=ROOT / "results/short-arcs", metavar="DIR")
    arguments = parser.parse_args()
    if arguments.extract is not None:
        extract(arguments.output, arguments.extract)
    elif arguments.verify:
        verify(arguments.output)
    else:
        build(arguments.output)


if __name__ == "__main__":
    main()
