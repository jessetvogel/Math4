def Function.injective (f : α → β) := ∀ {x y}, f x = f y → x = y

def Function.surjective (f : α → β) := ∀ y, ∃ x, f x = y

def Function.injective.comp {f : α → β} {g : β → γ} (hg : Function.injective g) (hf : Function.injective f) : Function.injective (g ∘ f) :=
  λ h => hf (hg h)

def Function.surjective.comp {f : α → β} {g : β → γ} (hg : Function.surjective g) (hf : Function.surjective f) : Function.surjective (g ∘ f) :=
  λ y => by match hg y with | Exists.intro z hz => match hf z with | Exists.intro x hx => apply Exists.intro x; rw [← hz, ← hx]; rfl;
