import tactic.ring

lemma foo {α : Type} [comm_ring α] (x y : α) : (x+y)^10 = (y+x)^10 :=
by ring