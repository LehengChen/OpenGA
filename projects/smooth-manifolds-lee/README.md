# Smooth Manifolds Lee Review Data

This project contains the review queue for the Lean formalization of Lee's
`Introduction to Smooth Manifolds`.

The textbook source archive used by the review app is tracked at:

```text
projects/smooth-manifolds-lee/sources/smooth-manifolds.zip
```

The review app uses that archive by default. To test a different local archive,
set:

```bash
export SMOOTH_MANIFOLDS_LEE_ZIP=/path/to/smooth-manifolds.zip
```

Lean source files are read from the git ref recorded in the tasks, currently
`origin/import/smooth-manifolds-lee`.

