import OpenGALib.Manifold.Charts.CoordinateBall
import OpenGALib.Manifold.Charts.PrecompactBasis
import OpenGALib.Manifold.Covering.LiftedStructure
import OpenGALib.Manifold.Covering.LocalSection
import OpenGALib.Manifold.Covering.ProperLocalDiffeomorph
import OpenGALib.Manifold.Covering.SmoothCoveringMap
import OpenGALib.Manifold.Instances.Pi
import OpenGALib.Manifold.Map.LocalDiffeomorph
import OpenGALib.Manifold.Map.TopologicalImmersionSubmersion
import OpenGALib.Manifold.Submanifold.Embedded
import OpenGALib.Manifold.Submanifold.SliceCharts
import OpenGALib.Manifold.Submanifold.TangentSpace

/-!
# Manifold

Manifold-foundations domain: chart-level and atlas-level structure on
topological and smooth manifolds, stated directly on Mathlib's
`ChartedSpace` / `IsManifold` API. Sits below `Riemannian` in the library
layering. Provides coordinate-ball predicates for charts, the inverse
function theorem with local-diffeomorphism characterizations for maps, the
point-set immersion/submersion conditions underlying them, the smooth
refinement of topological covering maps, immersed/embedded submanifold
structures with their tangent spaces, and the canonical manifold instance on
finite products.
-/
