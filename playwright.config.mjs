import {defineConfig} from '@playwright/test';
export default defineConfig({testDir:'./tests/browser',workers:1,timeout:120000,use:{headless:true},reporter:'list'});
