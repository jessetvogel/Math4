namespace Order

class Sup (α : Type _) where
  sup : α → α → α

infixl:80 " ⊔ " => Sup.sup

class Inf (α : Type _) where
  inf : α → α → α

infixl:80 " ⊓ " => Inf.inf

class Compl (α : Type _) where
  compl : α → α

postfix:max "ᶜ " => Compl.compl

class Top (α : Type _) where
  top : α

notation " ⊤ " => Top.top

class Bot (α : Type _) where
  bot : α

notation " ⊥ " => Bot.bot

end Order
