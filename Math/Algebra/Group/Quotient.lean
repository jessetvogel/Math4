import Math.Algebra.Group.Coset

namespace Algebra.Group

instance [G : Group α] (N : Subgroup G) [hN : N.normal] : Group (G.left_cosets N) := {
  mul := λ x y => by {
    -- Take a lift x' of x and a lift y' of y, then multiplication should be given
    -- by the image of x' * y'
    apply Quotient.lift _ _ x; intro x';
    apply Quotient.lift _ _ y; intro y';
    exact Quotient.mk _ (x' * y');
    -- Show that this is independent of the chosen representatives
    intro a b hab;
    cases hab with | intro n hn => {
      apply Quotient.sound;
      apply Exists.intro n ⟨hn.1, by rw [hn.2]; simp⟩;
    };
    intro a b hab;
    congr;
    funext c;
    apply Quotient.sound;
    cases hab with | intro n hn => {
      -- Use c⁻¹ * n * c
      apply Exists.intro (c⁻¹ * n * c);
      constructor;
      -- This element is in N because it is normal
      rw [← G.inv_inv c, G.inv_inv c⁻¹]; -- TODO: ugly, does n'th rewrite exist ?
      exact hN.has_conj _ _ hn.1; --(N.has_inv hn.1);
      rw [hn.2];
      simp;
    }
  },
  one := Quot.mk _ 1,
  mul_assoc := λ x y z => by {
    -- Take representatives of x, y and z
    match Quotient.exists_rep x, Quotient.exists_rep y, Quotient.exists_rep z with
    | Exists.intro x' hx', Exists.intro y' hy', Exists.intro z' hz' => {
      rw [← hx', ← hy', ← hz'];
      apply Quotient.sound;
      exact Exists.intro 1 ⟨N.has_one, by simp⟩;
    }
  },
  mul_one := λ x => by {
    cases Quotient.exists_rep x with | intro x' hx' => {
      rw [← hx'];
      apply Quotient.sound;
      apply Exists.intro;
      constructor;
      apply N.has_one; rfl;
    }
  },
  one_mul := λ x => by {
    cases Quotient.exists_rep x with | intro x' hx' => {
      rw [← hx'];
      apply Quotient.sound;
      apply Exists.intro;
      constructor;
      apply N.has_one; simp;
    }
  },
  inv := λ x => by {
    apply Quotient.lift _ _ x; intro x'; -- Take a lift x' of x
    apply Quotient.mk _ x'⁻¹; -- Then x⁻¹ is the image of x'⁻¹
    intro a b hab;
    apply Quotient.sound;
    cases hab with | intro n hn => {
      apply Exists.intro (b * n⁻¹ * b⁻¹);
      constructor;
      apply hN.has_conj;
      apply N.has_inv (hn.1);
      rw [hn.2];
      simp;
    }
  },
  mul_inv := λ x => by {
    cases Quotient.exists_rep x with | intro x' hx' => {
      rw [← hx'];
      apply Quotient.sound;
      apply Exists.intro;
      constructor;
      apply N.has_one;
      simp;
    }
  },
  inv_mul := λ x => by {
    cases Quotient.exists_rep x with | intro x' hx' => {
      rw [← hx'];
      apply Quotient.sound;
      apply Exists.intro;
      constructor;
      apply N.has_one;
      simp;
    }
  },
}

-- TODO: similarly for right_cosets

end Algebra.Group
