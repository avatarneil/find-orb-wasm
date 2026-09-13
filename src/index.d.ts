export interface CommandResult {
  files: Record<string, string>;
  stdout: string;
  exitCode: number;
}
export interface Session {
  /** Transfers ownership of the buffer. Call once before execute. */
  initialize(pack: ArrayBuffer, signal?: AbortSignal): Promise<{ready: true}>;
  /** Trusted CLI arguments; input/output text paths must be under /job/. */
  /** Outputs may include /job/name/ to collect up to 129 immediate regular files, each <=24 KB. */
  execute(args: string[], files: Record<string, string>, outputs: string[], signal?: AbortSignal): Promise<CommandResult>;
  /** Terminates active native code and rejects its pending promise. */
  close(message?: string): void;
}
export function createSession(workerSource: string, options?: {timeoutMs?: number}): Session;
