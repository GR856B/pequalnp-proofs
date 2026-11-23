import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_194

def picked (t : Fin 5 × Fin 4 × Fin 3 × Fin 2) : Fin 4 → Fin 5 :=
  let (a,b,c,d) := t
  ![a, a.succAbove b, a.succAbove (b.succAbove c), a.succAbove (b.succAbove (c.succAbove d))]

private lemma pickedInj : ∀ t, Function.Injective (picked t) := by decide +kernel

def emb (t : Fin 5 × Fin 4 × Fin 3 × Fin 2) : Fin 4 ↪ Fin 5 := ⟨picked t, pickedInj t⟩

private lemma bij : Function.Bijective emb := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro t u h
    have inj : ∀ t u, (∀ i, picked t i = picked u i) → t = u := by decide +kernel
    exact inj t u (fun i => DFunLike.congr_fun h i)
  · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_embedding_eq]
    decide

end PEqualNP.Outside.L_gct_194

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  let T (i j : ℕ) : ℂ := 1 + (if j = 4 then d * (if i = 0 then 1 else if i = 1 then -1 else 0)
    else c * (if i = j then 1 else if i = (j + 1) % 4 then Complex.I else if i = (j + 2) % 4 then -Complex.I else -1))
  change (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, T j (f j)) = 120
  let E := Equiv.ofBijective PEqualNP.Outside.L_gct_194.emb PEqualNP.Outside.L_gct_194.bij
  rw [← E.sum_comp (fun f => ∏ j : Fin 4, T j (f j))]
  simp only [Fintype.sum_prod_type, Fin.prod_univ_four]
  have t00 : T 0 0 = c + 1 := by norm_num [T] <;> ring
  have t01 : T 0 1 = 1 - c := by norm_num [T] <;> ring
  have t02 : T 0 2 = -c*Complex.I + 1 := by norm_num [T] <;> ring
  have t03 : T 0 3 = c*Complex.I + 1 := by norm_num [T] <;> ring
  have t04 : T 0 4 = d + 1 := by norm_num [T] <;> ring
  have t10 : T 1 0 = c*Complex.I + 1 := by norm_num [T] <;> ring
  have t11 : T 1 1 = c + 1 := by norm_num [T] <;> ring
  have t12 : T 1 2 = 1 - c := by norm_num [T] <;> ring
  have t13 : T 1 3 = -c*Complex.I + 1 := by norm_num [T] <;> ring
  have t14 : T 1 4 = 1 - d := by norm_num [T] <;> ring
  have t20 : T 2 0 = -c*Complex.I + 1 := by norm_num [T] <;> ring
  have t21 : T 2 1 = c*Complex.I + 1 := by norm_num [T] <;> ring
  have t22 : T 2 2 = c + 1 := by norm_num [T] <;> ring
  have t23 : T 2 3 = 1 - c := by norm_num [T] <;> ring
  have t24 : T 2 4 = 1 := by norm_num [T] <;> ring
  have t30 : T 3 0 = 1 - c := by norm_num [T] <;> ring
  have t31 : T 3 1 = -c*Complex.I + 1 := by norm_num [T] <;> ring
  have t32 : T 3 2 = c*Complex.I + 1 := by norm_num [T] <;> ring
  have t33 : T 3 3 = c + 1 := by norm_num [T] <;> ring
  have t34 : T 3 4 = 1 := by norm_num [T] <;> ring
  have expand : (∑ a : Fin 5, ∑ b : Fin 4, ∑ g : Fin 3, ∑ h : Fin 2, T 0 (E (a,b,g,h) 0) * T 1 (E (a,b,g,h) 1) * T 2 (E (a,b,g,h) 2) * T 3 (E (a,b,g,h) 3)) = ((((T 0 0 * T 1 1 * T 2 2 * T 3 3 + T 0 0 * T 1 1 * T 2 2 * T 3 4) + ((T 0 0 * T 1 1 * T 2 3 * T 3 2 + T 0 0 * T 1 1 * T 2 3 * T 3 4) + (T 0 0 * T 1 1 * T 2 4 * T 3 2 + T 0 0 * T 1 1 * T 2 4 * T 3 3))) + (((T 0 0 * T 1 2 * T 2 1 * T 3 3 + T 0 0 * T 1 2 * T 2 1 * T 3 4) + ((T 0 0 * T 1 2 * T 2 3 * T 3 1 + T 0 0 * T 1 2 * T 2 3 * T 3 4) + (T 0 0 * T 1 2 * T 2 4 * T 3 1 + T 0 0 * T 1 2 * T 2 4 * T 3 3))) + (((T 0 0 * T 1 3 * T 2 1 * T 3 2 + T 0 0 * T 1 3 * T 2 1 * T 3 4) + ((T 0 0 * T 1 3 * T 2 2 * T 3 1 + T 0 0 * T 1 3 * T 2 2 * T 3 4) + (T 0 0 * T 1 3 * T 2 4 * T 3 1 + T 0 0 * T 1 3 * T 2 4 * T 3 2))) + ((T 0 0 * T 1 4 * T 2 1 * T 3 2 + T 0 0 * T 1 4 * T 2 1 * T 3 3) + ((T 0 0 * T 1 4 * T 2 2 * T 3 1 + T 0 0 * T 1 4 * T 2 2 * T 3 3) + (T 0 0 * T 1 4 * T 2 3 * T 3 1 + T 0 0 * T 1 4 * T 2 3 * T 3 2)))))) + ((((T 0 1 * T 1 0 * T 2 2 * T 3 3 + T 0 1 * T 1 0 * T 2 2 * T 3 4) + ((T 0 1 * T 1 0 * T 2 3 * T 3 2 + T 0 1 * T 1 0 * T 2 3 * T 3 4) + (T 0 1 * T 1 0 * T 2 4 * T 3 2 + T 0 1 * T 1 0 * T 2 4 * T 3 3))) + (((T 0 1 * T 1 2 * T 2 0 * T 3 3 + T 0 1 * T 1 2 * T 2 0 * T 3 4) + ((T 0 1 * T 1 2 * T 2 3 * T 3 0 + T 0 1 * T 1 2 * T 2 3 * T 3 4) + (T 0 1 * T 1 2 * T 2 4 * T 3 0 + T 0 1 * T 1 2 * T 2 4 * T 3 3))) + (((T 0 1 * T 1 3 * T 2 0 * T 3 2 + T 0 1 * T 1 3 * T 2 0 * T 3 4) + ((T 0 1 * T 1 3 * T 2 2 * T 3 0 + T 0 1 * T 1 3 * T 2 2 * T 3 4) + (T 0 1 * T 1 3 * T 2 4 * T 3 0 + T 0 1 * T 1 3 * T 2 4 * T 3 2))) + ((T 0 1 * T 1 4 * T 2 0 * T 3 2 + T 0 1 * T 1 4 * T 2 0 * T 3 3) + ((T 0 1 * T 1 4 * T 2 2 * T 3 0 + T 0 1 * T 1 4 * T 2 2 * T 3 3) + (T 0 1 * T 1 4 * T 2 3 * T 3 0 + T 0 1 * T 1 4 * T 2 3 * T 3 2)))))) + ((((T 0 2 * T 1 0 * T 2 1 * T 3 3 + T 0 2 * T 1 0 * T 2 1 * T 3 4) + ((T 0 2 * T 1 0 * T 2 3 * T 3 1 + T 0 2 * T 1 0 * T 2 3 * T 3 4) + (T 0 2 * T 1 0 * T 2 4 * T 3 1 + T 0 2 * T 1 0 * T 2 4 * T 3 3))) + (((T 0 2 * T 1 1 * T 2 0 * T 3 3 + T 0 2 * T 1 1 * T 2 0 * T 3 4) + ((T 0 2 * T 1 1 * T 2 3 * T 3 0 + T 0 2 * T 1 1 * T 2 3 * T 3 4) + (T 0 2 * T 1 1 * T 2 4 * T 3 0 + T 0 2 * T 1 1 * T 2 4 * T 3 3))) + (((T 0 2 * T 1 3 * T 2 0 * T 3 1 + T 0 2 * T 1 3 * T 2 0 * T 3 4) + ((T 0 2 * T 1 3 * T 2 1 * T 3 0 + T 0 2 * T 1 3 * T 2 1 * T 3 4) + (T 0 2 * T 1 3 * T 2 4 * T 3 0 + T 0 2 * T 1 3 * T 2 4 * T 3 1))) + ((T 0 2 * T 1 4 * T 2 0 * T 3 1 + T 0 2 * T 1 4 * T 2 0 * T 3 3) + ((T 0 2 * T 1 4 * T 2 1 * T 3 0 + T 0 2 * T 1 4 * T 2 1 * T 3 3) + (T 0 2 * T 1 4 * T 2 3 * T 3 0 + T 0 2 * T 1 4 * T 2 3 * T 3 1)))))) + ((((T 0 3 * T 1 0 * T 2 1 * T 3 2 + T 0 3 * T 1 0 * T 2 1 * T 3 4) + ((T 0 3 * T 1 0 * T 2 2 * T 3 1 + T 0 3 * T 1 0 * T 2 2 * T 3 4) + (T 0 3 * T 1 0 * T 2 4 * T 3 1 + T 0 3 * T 1 0 * T 2 4 * T 3 2))) + (((T 0 3 * T 1 1 * T 2 0 * T 3 2 + T 0 3 * T 1 1 * T 2 0 * T 3 4) + ((T 0 3 * T 1 1 * T 2 2 * T 3 0 + T 0 3 * T 1 1 * T 2 2 * T 3 4) + (T 0 3 * T 1 1 * T 2 4 * T 3 0 + T 0 3 * T 1 1 * T 2 4 * T 3 2))) + (((T 0 3 * T 1 2 * T 2 0 * T 3 1 + T 0 3 * T 1 2 * T 2 0 * T 3 4) + ((T 0 3 * T 1 2 * T 2 1 * T 3 0 + T 0 3 * T 1 2 * T 2 1 * T 3 4) + (T 0 3 * T 1 2 * T 2 4 * T 3 0 + T 0 3 * T 1 2 * T 2 4 * T 3 1))) + ((T 0 3 * T 1 4 * T 2 0 * T 3 1 + T 0 3 * T 1 4 * T 2 0 * T 3 2) + ((T 0 3 * T 1 4 * T 2 1 * T 3 0 + T 0 3 * T 1 4 * T 2 1 * T 3 2) + (T 0 3 * T 1 4 * T 2 2 * T 3 0 + T 0 3 * T 1 4 * T 2 2 * T 3 1)))))) + (((T 0 4 * T 1 0 * T 2 1 * T 3 2 + T 0 4 * T 1 0 * T 2 1 * T 3 3) + ((T 0 4 * T 1 0 * T 2 2 * T 3 1 + T 0 4 * T 1 0 * T 2 2 * T 3 3) + (T 0 4 * T 1 0 * T 2 3 * T 3 1 + T 0 4 * T 1 0 * T 2 3 * T 3 2))) + (((T 0 4 * T 1 1 * T 2 0 * T 3 2 + T 0 4 * T 1 1 * T 2 0 * T 3 3) + ((T 0 4 * T 1 1 * T 2 2 * T 3 0 + T 0 4 * T 1 1 * T 2 2 * T 3 3) + (T 0 4 * T 1 1 * T 2 3 * T 3 0 + T 0 4 * T 1 1 * T 2 3 * T 3 2))) + (((T 0 4 * T 1 2 * T 2 0 * T 3 1 + T 0 4 * T 1 2 * T 2 0 * T 3 3) + ((T 0 4 * T 1 2 * T 2 1 * T 3 0 + T 0 4 * T 1 2 * T 2 1 * T 3 3) + (T 0 4 * T 1 2 * T 2 3 * T 3 0 + T 0 4 * T 1 2 * T 2 3 * T 3 1))) + ((T 0 4 * T 1 3 * T 2 0 * T 3 1 + T 0 4 * T 1 3 * T 2 0 * T 3 2) + ((T 0 4 * T 1 3 * T 2 1 * T 3 0 + T 0 4 * T 1 3 * T 2 1 * T 3 2) + (T 0 4 * T 1 3 * T 2 2 * T 3 0 + T 0 4 * T 1 3 * T 2 2 * T 3 1)))))))))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  apply expand.trans
  simp only [t00, t01, t02, t03, t04, t10, t11, t12, t13, t14, t20, t21, t22, t23, t24, t30, t31, t32, t33, t34]
  linear_combination (2*c^4*Complex.I^2 - 8*c^4*Complex.I + 2*c^4 + 24*c^2) * Complex.I_sq
