import Math.Algebra.Group.Basic
import Math.SetTheory.Basic

open SetTheory

namespace Algebra
namespace Group

structure Subgroup (G : Group α) where
  set : Set α
  has_one : 1 ∈ set
  has_mul : ∀ {x y}, x ∈ set → y ∈ set → (x * y) ∈ set
  has_inv : ∀ {x}, x ∈ set → x⁻¹ ∈ set

def Group.center (G : Group α) : Subgroup G := {
  set := λ x => ∀ y, x * y = y * x
  has_one := λ y => by simp,
  has_mul := λ {x y} hx hy z => by rw [← G.mul_assoc, hy z, G.mul_assoc, hx z, G.mul_assoc],
  has_inv := λ {x} hx y => by {
    apply G.cancel_left x;
    apply G.cancel_right x;
    rw [G.mul_assoc, G.mul_inv, G.one_mul, G.mul_assoc, ← G.mul_assoc, G.inv_mul, G.mul_one, hx];
  },
}

def Group.cyclic (G : Group α) (x : α) : Subgroup G := {
  set := λ y => ∃ (n : Int), y = x ^ n,
  has_one := Exists.intro 0 (by rfl),
  has_mul := λ {y z} hy hz => by {
    cases hy with | intro n₁ hy =>
    cases hz with | intro n₂ hz => {
      apply Exists.intro (n₁ + n₂);
      rw [G.zpow_add, hy, hz];
    }
  },
  has_inv := λ {y} hy => by {
    cases hy with | intro n hy => {
      apply Exists.intro (-n);
      simp [hy];
    }
  },
}

end Group
end Algebra
