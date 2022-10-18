import Math.Algebra.Group.Subgroup.Normal

open SetTheory

namespace Algebra.Group

def left_coset (G : Group α) (H : Subgroup G) (x : α) : Set α := λ y => ∃ (z : α), z ∈ H.set ∧ y = z * x

def right_coset (G : Group α) (H : Subgroup G) (x : α) : Set α := λ y => ∃ (z : α), z ∈ H.set ∧ y = x * z

def left_setoid {G : Group α} (H : Subgroup G) : Setoid α := {
  r := λ x y => ∃ (h : α), h ∈ H.set ∧ x = y * h
  iseqv := {
    refl := λ x => Exists.intro 1 ⟨H.has_one, by simp⟩,
    symm := λ (Exists.intro h hh) => Exists.intro h⁻¹ ⟨H.has_inv hh.1, by rw [hh.2]; simp⟩,
    trans := λ (Exists.intro h₁ hh₁) (Exists.intro h₂ hh₂) => Exists.intro (h₂ * h₁) ⟨H.has_mul hh₂.1 hh₁.1, by simp [hh₁, hh₂]⟩
  }
}

def right_setoid {G : Group α} (H : Subgroup G) : Setoid α := {
  r := λ x y => ∃ (h : α), h ∈ H.set ∧ x = h * y
  iseqv := {
    refl := λ x => Exists.intro 1 ⟨H.has_one, by simp⟩,
    symm := λ {x y} (Exists.intro h hh) => Exists.intro h⁻¹ ⟨H.has_inv hh.1, by rw [hh.2]; simp⟩,
    trans := λ {x y z} (Exists.intro h₁ hh₁) (Exists.intro h₂ hh₂) => Exists.intro (h₁ * h₂) ⟨H.has_mul hh₁.1 hh₂.1, by rw [hh₁.2, hh₂.2]; simp⟩
  }
}

def left_cosets (G : Group α) (H : Subgroup G) := Quotient (left_setoid H)

def right_cosets (G : Group α) (H : Subgroup G) := Quotient (right_setoid H)

end Algebra.Group
