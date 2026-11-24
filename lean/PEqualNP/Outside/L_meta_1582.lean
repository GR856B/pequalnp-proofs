import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1582 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  intro q m N L i0 T0 _ hm _ _ _ hinter _ hsub hcard
  have outside (t : Fin N) (ht : t ≠ i0) :
      m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
    have hs : T0.filter (fun x => x ∈ L t) ⊆ L i0 ∩ L t := by
      intro v hv
      obtain ⟨hv0, hvt⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_inter.mpr ⟨hsub hv0, hvt⟩
    have hle := Finset.card_le_card hs
    rw [hinter i0 t (Ne.symm ht)] at hle
    have hsum := Finset.card_filter_add_card_filter_not (s := T0) (fun x => x ∈ L t)
    omega
  have coline (t : Fin N) :
      (∃ v ∈ T0, decide (v ∉ L t) = true) ∨
        ∀ v : Fin N, v ∉ L i0 → decide (v ∉ L t) = true := by
    by_cases ht : t = i0
    · subst t
      exact Or.inr (fun v hv => decide_eq_true hv)
    · have hb := outside t ht
      have hp : 0 < (T0.filter (fun x => x ∉ L t)).card := by omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hp
      obtain ⟨hv0, hvt⟩ := Finset.mem_filter.mp hv
      exact Or.inl ⟨v, hv0, decide_eq_true hvt⟩
  refine ⟨?_, coline, outside, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with ⟨v, hv, h⟩ | h
    · exact Or.inl ⟨v, hv, hxy v h⟩
    · exact Or.inr (fun v hv => hxy v (h v hv))
  · intro x hx
    exact Or.inl ⟨x, hx, by simp⟩
  · exact Or.inr (fun v hv => decide_eq_true hv)
  · intro r _
    exact Or.inr (fun v hv => decide_eq_true (Or.inl hv))
  · intro t
    constructor
    · simp
    · intro p hp
      constructor
      · rcases coline t with ⟨v, hv, h⟩ | h
        · exact Or.inl ⟨v, hv, decide_eq_true (Or.inl (of_decide_eq_true h))⟩
        · exact Or.inr (fun v hv => decide_eq_true (Or.inl (of_decide_eq_true (h v hv))))
      · apply decide_eq_true
        exact ⟨p, hp, by simp⟩
