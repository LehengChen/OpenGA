import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import 'katex/dist/katex.min.css';
import styles from '../App.module.css';
import { isLeanLanguage, LeanCode } from './LeanCodeBlock';

type Props = {
  content: string;
};

const frontmatterRegex = /^---\s*\n[\s\S]*?\n---\s*(?:\n|$)/;

function stripFrontmatter(source: string): string {
  return source.replace(frontmatterRegex, '').trimStart();
}

function enhanceStructuralMarkers(source: string): string {
  // Make proof markers visually distinct: bold and separated from the
  // preceding statement paragraph.
  return source
    .replace(/\n\n(\*Proof\.\*|Proof\.)/g, '\n\n**Proof.** ')
    .replace(/^(\*Proof\.\*|Proof\.)/g, '**Proof.** ');
}

export function AtomViewer({ content }: Props) {
  const body = enhanceStructuralMarkers(stripFrontmatter(content));

  return (
    <div className={styles.atomContent}>
      <ReactMarkdown
        components={{
          code: ({ className, children }) => {
            const language = className?.match(/language-(\S+)/)?.[1];
            const code = String(children).replace(/\n$/, '');
            return isLeanLanguage(language) ? (
              <LeanCode code={code} language={language} className={className} />
            ) : (
              <code className={className}>{children}</code>
            );
          },
          img: ({ alt }) => (
            <span className={styles.omittedImage}>
              {alt ? `Image omitted: ${alt}` : 'Image omitted'}
            </span>
          )
        }}
        remarkPlugins={[remarkMath]}
        rehypePlugins={[rehypeKatex]}
      >
        {body}
      </ReactMarkdown>
    </div>
  );
}
