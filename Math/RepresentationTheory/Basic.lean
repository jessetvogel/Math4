import Math.Algebra.MonoidAlgebra.Basic
import Math.Algebra.Group.Basic
import Math.Algebra.Field.Basic
import Math.Algebra.Module.Basic

open Algebra

namespace RepresentationTheory

class abbrev Representation (k : Type _) [Field k] (G : Type _) [Group G] (V : Type _) := Module (MonoidAlgebra k G) V

end RepresentationTheory
