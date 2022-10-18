import Math.SetTheory.Basic

open SetTheory

namespace Topology

class Topology (α : Type u) where
  opens : Set (Set α)
  univ_open : Set.univ α ∈ opens
  empty_open : ∅ ∈ opens
  inter_open : ∀ U V, U ∈ opens → V ∈ opens → U ∩ V ∈ opens
  union_open : ∀ (S : Set (Set α)), S.subset opens → S.set_union ∈ opens

end Topology
