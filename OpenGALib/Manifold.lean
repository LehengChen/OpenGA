import OpenGALib.Manifold.Charts.CoordinateBall
import OpenGALib.Manifold.Charts.PrecompactBasis
import OpenGALib.Manifold.Map.LocalDiffeomorph

/-!
# Manifold

Manifold-foundations domain: chart-level and atlas-level structure on
topological and smooth manifolds, stated directly on Mathlib's
`ChartedSpace` / `IsManifold` API. Sits below `Riemannian` in the library
layering. Provides coordinate-ball predicates for charts and the inverse
function theorem with local-diffeomorphism characterizations for maps.
-/
