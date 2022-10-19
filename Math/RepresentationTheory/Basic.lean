import Math.Algebra.Group.Basic
import Math.Algebra.Field.Basic
import Math.Algebra.Module.Basic

open Algebra

namespace RepresentationTheory

-- TODO: define GroupRing
def Representation (α : Type u) [k : Field α] (β : Type v) [G : Group β] (γ : Type w) := Module (GroupRing k G) β

end RepresentationTheory
