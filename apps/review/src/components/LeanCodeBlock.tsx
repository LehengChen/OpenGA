import { useMemo } from 'react';
import styles from './LeanCodeBlock.module.css';

type TokenKind =
  | 'plain'
  | 'identifier'
  | 'comment'
  | 'string'
  | 'attribute'
  | 'keyword'
  | 'declaration'
  | 'namespace'
  | 'number'
  | 'symbol';

type Token = {
  kind: TokenKind;
  text: string;
};

type Expectation = 'declaration' | 'namespace' | null;

type Props = {
  code: string;
  language?: string;
  className?: string;
  'aria-label'?: string;
};

const keywords = new Set([
  'by',
  'calc',
  'case',
  'deriving',
  'do',
  'else',
  'extends',
  'for',
  'forall',
  'from',
  'fun',
  'have',
  'if',
  'import',
  'in',
  'let',
  'macro_rules',
  'match',
  'mutual',
  'open',
  'partial',
  'private',
  'protected',
  'return',
  'scoped',
  'set_option',
  'show',
  'termination_by',
  'then',
  'universe',
  'universes',
  'variable',
  'variables',
  'where',
  'with'
]);

const tacticKeywords = new Set([
  'apply',
  'assumption',
  'change',
  'constructor',
  'contradiction',
  'dsimp',
  'exact',
  'ext',
  'intro',
  'intros',
  'rfl',
  'rw',
  'simp',
  'simpa',
  'subst',
  'unfold'
]);

const declarationKeywords = new Set([
  'abbrev',
  'axiom',
  'class',
  'coinductive',
  'constant',
  'def',
  'elab',
  'example',
  'inductive',
  'instance',
  'lemma',
  'macro',
  'notation',
  'opaque',
  'structure',
  'syntax',
  'theorem'
]);

const namedDeclarationKeywords = new Set(
  [...declarationKeywords].filter((word) => word !== 'example' && word !== 'notation')
);

const namespaceKeywords = new Set(['end', 'import', 'namespace', 'open', 'section']);
const namespaceModifiers = new Set(['only', 'scoped']);

const tokenClassNames: Partial<Record<TokenKind, string>> = {
  attribute: styles.attribute,
  comment: styles.comment,
  declaration: styles.declaration,
  keyword: styles.keyword,
  namespace: styles.namespace,
  number: styles.number,
  string: styles.string,
  symbol: styles.symbol
};

export function isLeanLanguage(language: string | undefined): boolean {
  const normalized = language?.toLowerCase();
  return normalized === 'lean' || normalized === 'lean3' || normalized === 'lean4';
}

export function LeanCodeBlock({
  code,
  language = 'lean',
  className,
  'aria-label': ariaLabel
}: Props) {
  const tokens = useMemo(() => highlightLean(code), [code]);
  const blockClassName = className ? `${styles.block} ${className}` : styles.block;

  return (
    <pre className={blockClassName} data-language={language} aria-label={ariaLabel ?? 'Lean code'}>
      <code className={styles.code}>{renderTokenSpans(tokens)}</code>
    </pre>
  );
}

export function LeanCode({
  code,
  language = 'lean',
  className
}: Pick<Props, 'code' | 'language' | 'className'>) {
  const tokens = useMemo(() => highlightLean(code), [code]);

  return (
    <code className={className} data-language={language}>
      {renderTokenSpans(tokens)}
    </code>
  );
}

function renderTokenSpans(tokens: Token[]) {
  return tokens.map((token, index) => (
    <span key={index} className={tokenClassNames[token.kind]}>
      {token.text}
    </span>
  ));
}

function highlightLean(source: string): Token[] {
  return decorateTokens(tokenizeLean(source));
}

function decorateTokens(tokens: Token[]): Token[] {
  let expect: Expectation = null;

  return tokens.map((token) => {
    if (token.kind === 'plain') {
      if (token.text.includes('\n')) expect = null;
      return token;
    }

    if (token.kind === 'comment' || token.kind === 'attribute') {
      return token;
    }

    if (token.kind !== 'identifier') {
      if (expect) expect = null;
      return token;
    }

    const word = token.text;
    const isKeyword =
      keywords.has(word) || declarationKeywords.has(word) || namespaceKeywords.has(word) || tacticKeywords.has(word);

    if (isKeyword) {
      if (namedDeclarationKeywords.has(word)) {
        expect = 'declaration';
      } else if (namespaceKeywords.has(word)) {
        expect = 'namespace';
      } else if (expect === 'namespace' && namespaceModifiers.has(word)) {
        expect = 'namespace';
      } else {
        expect = null;
      }
      return { ...token, kind: 'keyword' };
    }

    if (expect) {
      const nextKind = expect;
      expect = null;
      return { ...token, kind: nextKind };
    }

    return token;
  });
}

function tokenizeLean(source: string): Token[] {
  const tokens: Token[] = [];
  let index = 0;

  while (index < source.length) {
    const char = source[index];
    const next = source[index + 1];

    if (isWhitespace(char)) {
      const start = index;
      while (index < source.length && isWhitespace(source[index])) index += 1;
      tokens.push({ kind: 'plain', text: source.slice(start, index) });
      continue;
    }

    if (char === '-' && next === '-') {
      const end = source.indexOf('\n', index);
      const nextIndex = end === -1 ? source.length : end;
      tokens.push({ kind: 'comment', text: source.slice(index, nextIndex) });
      index = nextIndex;
      continue;
    }

    if (char === '/' && next === '-') {
      const nextIndex = readBlockComment(source, index);
      tokens.push({ kind: 'comment', text: source.slice(index, nextIndex) });
      index = nextIndex;
      continue;
    }

    if (char === '@' && next === '[') {
      const nextIndex = readAttribute(source, index);
      tokens.push({ kind: 'attribute', text: source.slice(index, nextIndex) });
      index = nextIndex;
      continue;
    }

    if (char === '"') {
      const nextIndex = readString(source, index);
      tokens.push({ kind: 'string', text: source.slice(index, nextIndex) });
      index = nextIndex;
      continue;
    }

    if (char === '0' && /[xob]/i.test(next ?? '')) {
      const start = index;
      index += 2;
      while (index < source.length && /[0-9a-f_]/i.test(source[index])) index += 1;
      tokens.push({ kind: 'number', text: source.slice(start, index) });
      continue;
    }

    if (/[0-9]/.test(char)) {
      const start = index;
      index += 1;
      while (index < source.length && /[0-9_]/.test(source[index])) index += 1;
      if (source[index] === '.' && /[0-9]/.test(source[index + 1] ?? '')) {
        index += 1;
        while (index < source.length && /[0-9_]/.test(source[index])) index += 1;
      }
      tokens.push({ kind: 'number', text: source.slice(start, index) });
      continue;
    }

    if (char === '\u00ab') {
      const nextIndex = readQuotedIdentifier(source, index);
      tokens.push({ kind: 'identifier', text: source.slice(index, nextIndex) });
      index = nextIndex;
      continue;
    }

    if (isIdentifierStart(char)) {
      const start = index;
      index += 1;
      while (index < source.length && isIdentifierPart(source[index])) index += 1;
      tokens.push({ kind: 'identifier', text: source.slice(start, index) });
      continue;
    }

    const start = index;
    index += 1;
    while (
      index < source.length &&
      !isWhitespace(source[index]) &&
      !isIdentifierStart(source[index]) &&
      !/[0-9]/.test(source[index]) &&
      source[index] !== '"' &&
      source[index] !== '\u00ab' &&
      !(source[index] === '-' && source[index + 1] === '-') &&
      !(source[index] === '/' && source[index + 1] === '-') &&
      !(source[index] === '@' && source[index + 1] === '[')
    ) {
      index += 1;
    }
    tokens.push({ kind: 'symbol', text: source.slice(start, index) });
  }

  return tokens;
}

function readBlockComment(source: string, start: number): number {
  let depth = 0;
  let index = start;

  while (index < source.length) {
    if (source[index] === '/' && source[index + 1] === '-') {
      depth += 1;
      index += 2;
      continue;
    }

    if (source[index] === '-' && source[index + 1] === '/') {
      depth -= 1;
      index += 2;
      if (depth === 0) return index;
      continue;
    }

    index += 1;
  }

  return source.length;
}

function readAttribute(source: string, start: number): number {
  let depth = 0;
  let index = start;
  let inString = false;
  let escaped = false;

  while (index < source.length) {
    const char = source[index];

    if (inString) {
      escaped = !escaped && char === '\\';
      if (!escaped && char === '"') inString = false;
      if (char !== '\\') escaped = false;
      index += 1;
      continue;
    }

    if (char === '"') {
      inString = true;
    } else if (char === '[') {
      depth += 1;
    } else if (char === ']') {
      depth -= 1;
      if (depth === 0) return index + 1;
    }

    index += 1;
  }

  return source.length;
}

function readString(source: string, start: number): number {
  let index = start + 1;
  let escaped = false;

  while (index < source.length) {
    const char = source[index];
    if (!escaped && char === '"') return index + 1;
    escaped = !escaped && char === '\\';
    if (char !== '\\') escaped = false;
    index += 1;
  }

  return source.length;
}

function readQuotedIdentifier(source: string, start: number): number {
  const end = source.indexOf('\u00bb', start + 1);
  return end === -1 ? source.length : end + 1;
}

function isWhitespace(char: string): boolean {
  return /\s/.test(char);
}

function isIdentifierStart(char: string): boolean {
  return /[A-Za-z_]/.test(char) || char.charCodeAt(0) > 127;
}

function isIdentifierPart(char: string): boolean {
  return isIdentifierStart(char) || /[0-9'.?!]/.test(char);
}
