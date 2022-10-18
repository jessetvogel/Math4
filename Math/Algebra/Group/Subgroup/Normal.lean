import Math.Algebra.Group.Subgroup.Basic

namespace Algebra.Group

namespace Subgroup

class normal {G : Group α} (N : Subgroup G) : Prop where
  has_conj : ∀ n g, n ∈ N.set → (g * n * g⁻¹) ∈ N.set

end Subgroup

end Algebra.Group
