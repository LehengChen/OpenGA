export type TextbookEntry = {
  label?: string;
  env?: string;
  content?: string;
  dependencies?: string[];
  proof?: string | null;
};

export type LeanDeclaration = {
  kind: string;
  name: string;
  fullName: string;
  docstring: string | null;
  signature: string;
  sourceFile?: string;
};

export type LeanParsedCommand = {
  kind: string;
  namespaces: string[];
  startLine: number;
  startColumn: number;
  endLine: number;
  endColumn: number;
  text: string;
};
