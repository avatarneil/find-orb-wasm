// SPDX-License-Identifier: GPL-2.0-or-later
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp,mkdir,writeFile,readFile,readdir,rm,symlink} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {copyLockedFiles,cleanBuildEnvironment,digest} from '../../build/build.mjs';

test('only locked regular inputs enter the fresh compiler tree',async t=>{
  const work=await mkdtemp(join(tmpdir(),'fo-source-integrity-'));t.after(()=>rm(work,{recursive:true,force:true}));
  const source=join(work,'input'),target=join(work,'compiled');await mkdir(source);
  await writeFile(join(source,'makefile'),'trusted recipe');
  await writeFile(join(source,'GNUmakefile'),'unlisted preferred recipe');
  await writeFile(join(source,'foreign.a'),'unlisted archive member');
  const files={makefile:digest('trusted recipe')};
  await copyLockedFiles(source,target,files);
  assert.deepEqual(await readdir(target),['makefile']);
  assert.equal(await readFile(join(target,'makefile'),'utf8'),'trusted recipe');
  await writeFile(join(source,'makefile'),'changed recipe');
  await assert.rejects(copyLockedFiles(source,target,files),/integrity mismatch/);
  await symlink(join(source,'GNUmakefile'),join(source,'link'));
  await assert.rejects(copyLockedFiles(source,target,{link:digest('unlisted preferred recipe')}),/integrity mismatch/);
  await assert.rejects(copyLockedFiles(source,target,{'../outside':digest('x')}),/Unsafe source-lock/);
});

test('ambient make and compiler overrides cannot defeat the recorded policy',()=>{
  const poisoned={PATH:'/usr/bin',HOME:'/home/example',CXXFLAGS:'-ffast-math',CFLAGS:'-ffast-math',CPPFLAGS:'-I /foreign',
    ADDED_CFLAGS:'-ffp-contract=fast',MAKEFLAGS:'--environment-overrides',MFLAGS:'-e',MAKEFILES:'/foreign/makefile',
    EMCC_CFLAGS:'-ffast-math',CPATH:'/foreign',CXX:'unrecorded-compiler'};
  assert.deepEqual(cleanBuildEnvironment(poisoned),{PATH:'/usr/bin',HOME:'/home/example'});
  assert.equal(poisoned.CXXFLAGS,'-ffast-math','Does not change caller environment');
});
