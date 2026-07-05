import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dump, load } from 'js-yaml';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const projectRoot = path.resolve(__dirname, '../../..');
const importRef = process.env.SMOOTH_MANIFOLDS_LEE_IMPORT_REF ?? 'origin/import/smooth-manifolds-lee';
const textbookZipPath =
  process.env.SMOOTH_MANIFOLDS_LEE_ZIP ??
  path.join(projectRoot, 'projects/smooth-manifolds-lee/sources/smooth-manifolds.zip');
const jsonPrefix =
  'sections-1to8-Introduction-to-Smooth-Manifolds-Second-Edition-2013-by-John-M.-Lee';
const taskDir = path.join(projectRoot, 'projects/smooth-manifolds-lee/tasks');
const outputPath = path.join(taskDir, 'all.tasks.yaml');
const reportPath = path.join(taskDir, 'generation-report.json');
const previousTaskPaths = [outputPath, path.join(taskDir, 'section01.tasks.yaml')];

function run(command, args, options = {}) {
  return execFileSync(command, args, {
    cwd: projectRoot,
    encoding: 'utf-8',
    maxBuffer: 80 * 1024 * 1024,
    ...options
  });
}

function safeReadYaml(filePath) {
  if (!fs.existsSync(filePath)) return null;
  return load(fs.readFileSync(filePath, 'utf-8'));
}

function previousTasksById() {
  const map = new Map();
  for (const filePath of previousTaskPaths) {
    const dataset = safeReadYaml(filePath);
    for (const task of dataset?.tasks ?? []) {
      if (!map.has(task.id)) map.set(task.id, task);
    }
  }
  return map;
}

function zipJsonEntries() {
  return run('unzip', ['-Z1', textbookZipPath])
    .split(/\r?\n/)
    .filter((entry) => entry.startsWith(`${jsonPrefix}/section`) && entry.endsWith('.json'))
    .sort();
}

function loadTextbookSections() {
  const sections = new Map();
  for (const entryPath of zipJsonEntries()) {
    const match = entryPath.match(/section(\d+)\.json$/);
    if (!match) continue;
    const sectionNumber = Number(match[1]);
    const raw = run('unzip', ['-p', textbookZipPath, entryPath]);
    const entries = JSON.parse(raw);
    const labels = new Map();
    for (const [index, entry] of entries.entries()) {
      if (entry.label) labels.set(entry.label, { entry, index });
    }
    sections.set(sectionNumber, { entryPath, entries, labels });
  }
  return sections;
}

function leanPaths() {
  return run('git', ['ls-tree', '-r', '--name-only', importRef])
    .split(/\r?\n/)
    .filter((item) =>
      /^staging\/SmoothManifoldsLee\/SmoothManifoldsLee\/Chap\d+\/.+\.lean$/.test(item)
    )
    .sort();
}

function sectionNumberFromPath(leanPath) {
  const sectionPart = leanPath.split('/')[4];
  const numbers = sectionPart.match(/\d+/g) ?? [];
  return Number(numbers[numbers.length - 1]);
}

function chapterNumberFromPath(leanPath) {
  const chapterPart = leanPath.split('/')[3];
  return Number(chapterPart.replace(/^Chap0*/, ''));
}

function labelFromLeanFilename(fileName) {
  const parts = fileName.replace(/\.lean$/, '').split('_');
  const kind = parts.shift();
  const extraIndex = parts.indexOf('extra');
  if (extraIndex !== -1) {
    const number = parts.slice(0, extraIndex).join('.');
    const suffix = parts.slice(extraIndex + 1).join('-');
    return `${kind} ${number}-extra-${suffix}`;
  }
  if (!parts.every((part) => /^\d+$/.test(part))) return null;
  const separator = kind === 'Problem' ? '-' : '.';
  return `${kind} ${parts.join(separator)}`;
}

function addSupportingLeanFile(map, ownerPath, leanPath, relation) {
  if (!map.has(ownerPath)) map.set(ownerPath, []);
  map.get(ownerPath).push(leanPath);
  return { path: leanPath, owner: ownerPath, relation };
}

function nestedOwnerPath(leanPath) {
  const parts = leanPath.split('/');
  if (parts.length <= 6) return null;
  return `${parts.slice(0, 5).join('/')}/${parts[5]}.lean`;
}

function topLevelOwnerForAuxLean(leanPath, topLevelLeanSet) {
  const dir = path.dirname(leanPath);
  const stemParts = path.basename(leanPath, '.lean').split('_');
  for (let end = stemParts.length - 1; end >= 2; end--) {
    const ownerStem = stemParts.slice(0, end).join('_');
    const ownerPath = `${dir}/${ownerStem}.lean`;
    if (
      ownerPath !== leanPath &&
      topLevelLeanSet.has(ownerPath) &&
      labelFromLeanFilename(`${ownerStem}.lean`)
    ) {
      return ownerPath;
    }
  }
  return null;
}

function slug(input) {
  return input
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '');
}

function chapterId(chapterNumber) {
  return `sml.ch${chapterNumber}`;
}

function sectionId(chapterNumber, sectionNumber) {
  return `sml.ch${chapterNumber}.sec${sectionNumber}`;
}

function taskId(chapterNumber, sectionNumber, label) {
  return `${sectionId(chapterNumber, sectionNumber)}.${slug(label)}`;
}

function dcref(label) {
  const [kind, ...rest] = label.split(' ');
  return `lee-sm:${kind.toLowerCase()}:${rest.join(' ').toLowerCase()}`;
}

function sectionTitle(sectionNumber, sectionInfo) {
  const context = sectionInfo.entries[0]?.context;
  const raw = context?.section ?? `Section ${sectionNumber}`;
  return raw.replace(/^\d+\.?\s*/, '') || raw;
}

function chapterTitle(chapterNumber, sectionInfos) {
  for (const info of sectionInfos) {
    const title = info.entries[0]?.context?.chapter;
    if (title) return title;
  }
  return `Chapter ${chapterNumber}`;
}

function emptyGithub() {
  return { issue: null, pr: null, discussion: null };
}

function mergeReviewState(task, previous) {
  if (!previous) return task;
  const checks = task.kind === 'leaf'
    ? {
        informal_review: previous.checks?.informal_review ?? task.checks.informal_review,
        formal_review: previous.checks?.formal_review ?? task.checks.formal_review
      }
    : task.checks;

  return {
    ...task,
    status: previous.status ?? task.status,
    checks,
    review_notes: previous.review_notes ?? task.review_notes,
    github: previous.github ?? task.github
  };
}

function buildCandidates(sections) {
  const candidates = [];
  const unmatchedTopLevelLean = [];
  const nestedAuxLean = [];
  const unattachedNestedAuxLean = [];
  const attachedAuxLean = [];
  const supportingLeanByOwner = new Map();
  const paths = leanPaths();
  const topLevelLeanPaths = paths.filter((leanPath) => leanPath.split('/').length === 6);
  const topLevelLeanSet = new Set(topLevelLeanPaths);

  for (const leanPath of paths) {
    const parts = leanPath.split('/');
    if (parts.length > 6) {
      nestedAuxLean.push(leanPath);
      const ownerPath = nestedOwnerPath(leanPath);
      if (ownerPath && topLevelLeanSet.has(ownerPath)) {
        attachedAuxLean.push(
          addSupportingLeanFile(supportingLeanByOwner, ownerPath, leanPath, 'nested')
        );
      } else {
        unattachedNestedAuxLean.push({
          path: leanPath,
          owner: ownerPath,
          reason: 'top-level owner not found'
        });
      }
      continue;
    }

    const label = labelFromLeanFilename(parts[5]);
    if (!label) {
      const ownerPath = topLevelOwnerForAuxLean(leanPath, topLevelLeanSet);
      if (ownerPath) {
        attachedAuxLean.push(
          addSupportingLeanFile(supportingLeanByOwner, ownerPath, leanPath, 'noncanonical-top-level')
        );
      }
    }
  }

  for (const leanPath of topLevelLeanPaths) {
    const parts = leanPath.split('/');
    const label = labelFromLeanFilename(parts[5]);
    const sectionNumber = sectionNumberFromPath(leanPath);
    const chapterNumber = chapterNumberFromPath(leanPath);
    const sectionInfo = sections.get(sectionNumber);
    if (!label) {
      if (!topLevelOwnerForAuxLean(leanPath, topLevelLeanSet)) {
        unmatchedTopLevelLean.push({
          path: leanPath,
          reason: 'noncanonical filename',
          action: 'manual classification required'
        });
      }
      continue;
    }
    const labelInfo = sectionInfo?.labels.get(label);
    if (!labelInfo) {
      unmatchedTopLevelLean.push({
        path: leanPath,
        label,
        section: sectionNumber,
        reason: 'label not in section JSON',
        action: 'manual textbook label or synthetic task required'
      });
      continue;
    }

    candidates.push({
      chapterNumber,
      sectionNumber,
      label,
      leanPath,
      supportingLeanPaths: supportingLeanByOwner.get(leanPath) ?? [],
      jsonPath: sectionInfo.entryPath,
      jsonIndex: labelInfo.index,
      context: labelInfo.entry.context ?? {}
    });
  }

  candidates.sort((a, b) =>
    a.chapterNumber - b.chapterNumber ||
    a.sectionNumber - b.sectionNumber ||
    a.jsonIndex - b.jsonIndex ||
    a.label.localeCompare(b.label)
  );

  return {
    candidates,
    unmatchedTopLevelLean,
    nestedAuxLean,
    attachedAuxLean,
    unattachedNestedAuxLean
  };
}

function buildDataset(candidates, sections, previous) {
  const tasks = [];
  const chapterNumbers = [...new Set(candidates.map((item) => item.chapterNumber))];
  const sectionNumbersByChapter = new Map();
  const candidatesBySection = new Map();

  for (const candidate of candidates) {
    const key = `${candidate.chapterNumber}:${candidate.sectionNumber}`;
    if (!candidatesBySection.has(key)) candidatesBySection.set(key, []);
    candidatesBySection.get(key).push(candidate);
    if (!sectionNumbersByChapter.has(candidate.chapterNumber)) {
      sectionNumbersByChapter.set(candidate.chapterNumber, new Set());
    }
    sectionNumbersByChapter.get(candidate.chapterNumber).add(candidate.sectionNumber);
  }

  const book = {
    id: 'sml.book',
    kind: 'root',
    parent: null,
    depends_on: [],
    unlocks: chapterNumbers.map(chapterId),
    dcref: null,
    chapter: null,
    title: 'Lee — Introduction to Smooth Manifolds',
    description: 'Review textbook-aligned Lean formalization tasks before deciding what should be ported into OpenGALib.',
    status: 'todo',
    checks: {},
    review_notes: [],
    files: {},
    editable: [],
    github: emptyGithub()
  };
  tasks.push(mergeReviewState(book, previous.get(book.id)));

  for (const chapterNumber of chapterNumbers) {
    const sectionNumbers = [...sectionNumbersByChapter.get(chapterNumber)].sort((a, b) => a - b);
    const sectionInfos = sectionNumbers.map((sectionNumber) => sections.get(sectionNumber));
    const chapter = {
      id: chapterId(chapterNumber),
      kind: 'cluster',
      parent: 'sml.book',
      depends_on: [],
      unlocks: sectionNumbers.map((sectionNumber) => sectionId(chapterNumber, sectionNumber)),
      dcref: null,
      chapter: chapterNumber,
      title: `Chapter ${chapterNumber} — ${chapterTitle(chapterNumber, sectionInfos)}`,
      description: `Chapter ${chapterNumber} entries paired with imported SmoothManifoldsLee Lean files.`,
      status: 'todo',
      checks: {},
      review_notes: [],
      files: {},
      editable: [],
      github: emptyGithub()
    };
    tasks.push(mergeReviewState(chapter, previous.get(chapter.id)));

    for (const sectionNumber of sectionNumbers) {
      const key = `${chapterNumber}:${sectionNumber}`;
      const items = candidatesBySection.get(key);
      const sectionInfo = sections.get(sectionNumber);
      const section = {
        id: sectionId(chapterNumber, sectionNumber),
        kind: 'cluster',
        parent: chapter.id,
        depends_on: [],
        unlocks: items.map((item) => taskId(chapterNumber, sectionNumber, item.label)),
        dcref: `lee-sm:${chapterNumber}.${sectionNumber}`,
        chapter: chapterNumber,
        title: `Section ${sectionNumber} — ${sectionTitle(sectionNumber, sectionInfo)}`,
        description: `Textbook section ${sectionNumber} entries paired with imported Lean files.`,
        status: 'todo',
        checks: {},
        review_notes: [],
        files: { textbook_json: sectionInfo.entryPath },
        editable: [],
        github: emptyGithub()
      };
      tasks.push(mergeReviewState(section, previous.get(section.id)));

      for (const item of items) {
        const id = taskId(chapterNumber, sectionNumber, item.label);
        const leanFiles = [item.leanPath, ...item.supportingLeanPaths];
        const source = {
          textbook_json: item.jsonPath,
          textbook_label: item.label,
          import_ref: importRef,
          lean_file: item.leanPath
        };
        if (leanFiles.length > 1) {
          source.lean_files = leanFiles;
        }
        const task = {
          id,
          kind: 'leaf',
          parent: section.id,
          depends_on: [],
          unlocks: [],
          dcref: dcref(item.label),
          chapter: chapterNumber,
          title: item.label,
          description: `Textbook source and Lean file review for ${item.label}.`,
          status: 'todo',
          checks: {
            informal_review: 'pending',
            formal_review: 'pending'
          },
          review_notes: [],
          files: {
            textbook_json: item.jsonPath,
            lean_source: item.leanPath
          },
          editable: [],
          github: emptyGithub(),
          review_kind: 'lean_textbook',
          source
        };
        tasks.push(mergeReviewState(task, previous.get(id)));
      }
    }
  }

  return {
    schema: 'openga-review.tasks.v2',
    project: 'smooth-manifolds-lee',
    title: 'Smooth Manifolds Lee',
    description: 'Semantic review queue for Lee textbook-aligned Lean formalization tasks.',
    review_kind: 'lean_textbook',
    tasks
  };
}

function report(
  candidates,
  sections,
  unmatchedTopLevelLean,
  nestedAuxLean,
  attachedAuxLean,
  unattachedNestedAuxLean
) {
  const matchedLabels = new Set(candidates.map((item) => `${item.sectionNumber}\t${item.label}`));
  const importedSections = new Set(candidates.map((item) => item.sectionNumber));
  const jsonWithoutLean = [];
  const jsonOutsideImportedSections = [];
  for (const [sectionNumber, sectionInfo] of sections) {
    for (const label of sectionInfo.labels.keys()) {
      if (!matchedLabels.has(`${sectionNumber}\t${label}`)) {
        const target = importedSections.has(sectionNumber)
          ? jsonWithoutLean
          : jsonOutsideImportedSections;
        target.push({ section: sectionNumber, label });
      }
    }
  }

  const countBy = (items, keyFn) =>
    Object.fromEntries(
      [...items.reduce((map, item) => {
        const key = keyFn(item);
        map.set(key, (map.get(key) ?? 0) + 1);
        return map;
      }, new Map())].sort((a, b) => String(a[0]).localeCompare(String(b[0])))
    );

  return {
    importRef,
    textbookZipPath,
    generatedReviewTasks: candidates.length,
    matchedByChapter: countBy(candidates, (item) => `chapter${item.chapterNumber}`),
    matchedBySection: countBy(candidates, (item) => `section${String(item.sectionNumber).padStart(2, '0')}`),
    unmatchedTopLevelLean,
    nestedAuxLean,
    attachedAuxLean,
    unattachedNestedAuxLean,
    jsonLabelsWithoutLean: jsonWithoutLean,
    jsonLabelsOutsideImportedSections: jsonOutsideImportedSections,
    notes: [
      'Auxiliary Lean files are attached to their canonical owner task when a matching owner exists.',
      'JSON entries without matching Lean files inside imported sections are reported but do not block review generation.',
      'JSON entries outside imported sections are separated from the current Ch1-Ch5 review queue.'
    ]
  };
}

fs.mkdirSync(taskDir, { recursive: true });
const sections = loadTextbookSections();
const previous = previousTasksById();
const {
  candidates,
  unmatchedTopLevelLean,
  nestedAuxLean,
  attachedAuxLean,
  unattachedNestedAuxLean
} = buildCandidates(sections);
const dataset = buildDataset(candidates, sections, previous);
const yamlText = dump(dataset, { indent: 2, lineWidth: -1, seqNoIndent: true, sortKeys: false });
const reportText = JSON.stringify(
  report(candidates, sections, unmatchedTopLevelLean, nestedAuxLean, attachedAuxLean, unattachedNestedAuxLean),
  null,
  2
);
fs.writeFileSync(outputPath, yamlText, 'utf-8');
fs.writeFileSync(reportPath, `${reportText}\n`, 'utf-8');

console.log(`Generated ${candidates.length} SmoothManifoldsLee review tasks.`);
console.log(`Wrote ${path.relative(projectRoot, outputPath)}`);
console.log(`Wrote ${path.relative(projectRoot, reportPath)}`);
