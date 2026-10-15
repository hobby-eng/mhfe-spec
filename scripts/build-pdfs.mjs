#!/usr/bin/env node
import { execFileSync } from "node:child_process";
import { mkdirSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const args = process.argv.slice(2);
try {
  if (args.length === 1 && args[0] === "--local") {
    const { PdfBuild } = await import("./pdf/build.mjs");
    await new PdfBuild(root).run();
  } else if (!args.length) {
    const image = "mhfe-spec-pdf:local";
    const output = resolve(root, "output");
    mkdirSync(output, { recursive: true });
    execFileSync(
      "docker",
      ["build", "--tag", image, "--file", "tooling/pdf/Dockerfile", "tooling/pdf"],
      { cwd: root, stdio: "inherit" },
    );
    execFileSync(
      "docker",
      [
        "run",
        "--rm",
        "--network",
        "none",
        "--cap-drop",
        "ALL",
        "--security-opt",
        "no-new-privileges",
        "--memory",
        "2g",
        "--cpus",
        "2",
        "--pids-limit",
        "256",
        "--shm-size",
        "256m",
        "--user",
        `${process.getuid()}:${process.getgid()}`,
        "--env",
        "HOME=/tmp",
        "--mount",
        `type=bind,source=${root},target=/work,readonly`,
        "--mount",
        `type=bind,source=${output},target=/work/output`,
        image,
        "node",
        "scripts/build-pdfs.mjs",
        "--local",
      ],
      { stdio: "inherit" },
    );
  } else {
    throw new Error("Usage: node scripts/build-pdfs.mjs [--local]");
  }
} catch (error) {
  console.error(`MHFE PDF · failed: ${error.message}`);
  process.exitCode = 1;
}
