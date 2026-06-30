import { Component, type ErrorInfo, type ReactNode } from 'react';
import styles from '../App.module.css';

type Props = {
  children: ReactNode;
};

type State = {
  error: Error | null;
  stack: string | null;
};

export class ErrorBoundary extends Component<Props, State> {
  state: State = {
    error: null,
    stack: null
  };

  static getDerivedStateFromError(error: Error): State {
    return { error, stack: error.stack ?? null };
  }

  componentDidCatch(error: Error, info: ErrorInfo): void {
    console.error('Review app render error', error, info.componentStack);
    this.setState({
      error,
      stack: error.stack ?? info.componentStack ?? null
    });
  }

  render() {
    if (!this.state.error) return this.props.children;

    return (
      <main className={styles.appShell}>
        <section className={styles.runtimeErrorPanel} role="alert">
          <p className={styles.kicker}>Review app error</p>
          <h1>Frontend render failed</h1>
          <p className={styles.detailSummary}>
            The app hit a browser-side rendering error. The message below is shown here so the page
            does not fail as a blank screen.
          </p>
          <pre>
            <code>
              {this.state.error.message}
              {this.state.stack ? `\n\n${this.state.stack}` : ''}
            </code>
          </pre>
        </section>
      </main>
    );
  }
}
