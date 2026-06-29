import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import styles from '../App.module.css';

type Props = {
  content: string;
};

const frontmatterRegex = /^---\s*\n[\s\S]*?\n---\s*(?:\n|$)/;

function stripFrontmatter(source: string): string {
  return source.replace(frontmatterRegex, '').trimStart();
}

export function AtomViewer({ content }: Props) {
  const body = stripFrontmatter(content);

  return (
    <div className={styles.atomContent}>
      <ReactMarkdown remarkPlugins={[remarkMath]} rehypePlugins={[rehypeKatex]}>
        {body}
      </ReactMarkdown>
    </div>
  );
}
