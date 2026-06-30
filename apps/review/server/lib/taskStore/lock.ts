class Mutex {
  private locked = false;
  private queue: Array<() => void> = [];

  async acquire(): Promise<() => void> {
    return new Promise((resolve) => {
      const release = () => {
        const next = this.queue.shift();
        if (next) {
          next();
        } else {
          this.locked = false;
        }
      };

      if (!this.locked) {
        this.locked = true;
        resolve(release);
      } else {
        this.queue.push(() => resolve(release));
      }
    });
  }
}

const writeLock = new Mutex();

export async function withTaskLock<T>(fn: () => T | Promise<T>): Promise<T> {
  const release = await writeLock.acquire();
  try {
    return await fn();
  } finally {
    release();
  }
}
