import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G _ hfour U hU x Y hY R π hblocks hcover
  classical
  have adjY (y : Fin n) (hy : y ∈ Y) : G.Adj x y := hU _ (hY y hy)
  have separate (B : Finset (Fin n)) (hB : B ∈ π) (a b : Fin n)
      (ha : a ∈ B) (hb : b ∈ B) (hxa : G.Adj x a) (hxb : G.Adj x b)
      (hit : a ∈ Y ∨ b ∈ Y) : a = b := by
    rcases (hblocks B hB).2 with hone | ⟨_, c, hc, hoff⟩
    · exact Finset.card_le_one_iff.mp hone.le ha hb
    · have hne : x ≠ c := by
        intro heq
        subst c
        rcases hit with h | h
        · exact hoff a ha (hY a h)
        · exact hoff b hb (hY b h)
      apply Finset.card_le_one_iff.mp (hfour x c hne)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa, hc a ha⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb, hc b hb⟩
  have count (S : Finset (Fin n)) (hs : S ⊆ R) (hadj : ∀ v ∈ S, G.Adj x v)
      (hy : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a ∈ Y ∨ b ∈ Y) : S.card ≤ π.card := by
    have existsBlock (v : S) : ∃ B : π, v.val ∈ B.val := by
      obtain ⟨B, hB, hv⟩ := hcover v.val (hs v.property)
      exact ⟨⟨B, hB⟩, hv⟩
    choose pick hmem using existsBlock
    apply Finset.card_le_card_of_injective (f := pick)
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have hb : b.val ∈ (pick a).val := hab ▸ hmem b
    exact hne (separate _ (pick a).property _ _ (hmem a) hb
      (hadj _ a.property) (hadj _ b.property) (hy _ a.property _ b.property hne))
  constructor
  · apply count (R ∩ Y) Finset.inter_subset_left
    · exact fun v hv => adjY v (Finset.mem_inter.mp hv).2
    · exact fun a ha _ _ _ => Or.inl (Finset.mem_inter.mp ha).2
  · intro hR hnot
    obtain ⟨z, hzR, hzY⟩ := Finset.not_subset.mp hnot
    have hz : z ∉ R ∩ Y := fun h => hzY (Finset.mem_inter.mp h).2
    rw [← Finset.card_insert_of_notMem hz]
    have hs : insert z (R ∩ Y) ⊆ R := Finset.insert_subset hzR Finset.inter_subset_left
    apply count _ hs (fun v hv => hR v (hs hv))
    intro a ha b hb hne
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with h | hb
      · exact False.elim (hne h.symm)
      · exact Or.inr (Finset.mem_inter.mp hb).2
    · exact Or.inl (Finset.mem_inter.mp ha).2
