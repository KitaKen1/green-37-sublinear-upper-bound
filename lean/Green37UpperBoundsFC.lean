import FormalConjectures.GreensOpenProblems.«37»

/-!
# Green 37: fixed periodic CRT covers

This file fills the registered `green_37_littleO` and `green_37_bigO` answers with
`N ↦ N`.  The proof uses shifted Fermat numbers as pairwise-coprime moduli and
cuts a fixed sparse periodic cover to a finite interval.
-/

open Set Filter Finset
open scoped Asymptotics BigOperators ENat

namespace Green37Proof

noncomputable section

lemma containsAP_of_mem {A : Set ℕ} {k d a : ℕ} (hd : 0 < d)
    (hmem : ∀ j < k, a + j * d ∈ A) : Set.ContainsAP A k d := by
  let f : Fin k → ℕ := fun j ↦ a + j * d
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    simp only [f] at hij
    exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_left_cancel hij)
  refine ⟨a, Set.range f, ?_, ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact hmem j j.isLt
  · constructor
    · calc
        ENat.card (Set.range f) = ENat.card (Fin k) :=
          (ENat.card_congr (Equiv.ofInjective f hf)).symm
        _ = k := by simp
    · ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j, by simp, by simp [f]⟩
      · rintro ⟨n, hn, rfl⟩
        have hnk : n < k := by exact_mod_cast hn
        exact ⟨⟨n, hnk⟩, by simp [f]⟩

def modulus (t : ℕ) {k : ℕ} (j : Fin k) : ℕ := Nat.fermatNumber (t + j)

lemma modulus_pos (t : ℕ) {k : ℕ} (j : Fin k) : 0 < modulus t j := by
  exact (Nat.two_lt_fermatNumber _).trans_le' (by omega)

lemma moduli_pairwise (t k : ℕ) :
    (List.finRange k).Pairwise (Function.onFun Nat.Coprime (fun j ↦ modulus t j)) := by
  apply (List.nodup_finRange k).pairwise_of_forall_ne
  intro i _ j _ hij
  apply Nat.coprime_fermatNumber_fermatNumber
  intro h
  apply hij
  apply Fin.ext
  simpa [modulus] using Nat.add_left_cancel h

def residue (t d : ℕ) {k : ℕ} (j : Fin k) : ℕ :=
  let q := modulus t j
  q * (j * d / q + 1) - j * d

def start (t k d : ℕ) : ℕ :=
  Nat.chineseRemainderOfList (residue t d) (modulus t) (List.finRange k)
    (moduli_pairwise t k)

def period (t k : ℕ) : ℕ := ((List.finRange k).map (modulus t)).prod

lemma start_lt_period (t k d : ℕ) : start t k d < period t k := by
  exact Nat.chineseRemainderOfList_lt_prod _ _ _ _
    (fun j _ ↦ (modulus_pos t j).ne')

lemma modulus_dvd_start_add (t k d : ℕ) (j : Fin k) :
    modulus t j ∣ start t k d + j * d := by
  let q := modulus t j
  let r := j * d
  have hrle : r ≤ q * (r / q + 1) := by
    have hq : 0 < q := modulus_pos t j
    exact (Nat.lt_mul_div_succ r hq).le
  have hsum : residue t d j + r = q * (r / q + 1) := by
    simp only [residue, q, r]
    exact Nat.sub_add_cancel hrle
  have hcrt : start t k d ≡ residue t d j [MOD q] := by
    exact (Nat.chineseRemainderOfList (residue t d) (modulus t) (List.finRange k)
      (moduli_pairwise t k)).prop j (List.mem_finRange j)
  have hz : residue t d j + r ≡ 0 [MOD q] := by
    rw [Nat.modEq_zero_iff_dvd, hsum]
    exact dvd_mul_right _ _
  exact Nat.modEq_zero_iff_dvd.mp ((hcrt.add_right r).trans hz)

def coverLength (t k N : ℕ) : ℕ := period t k + k * N

def multiplesBelow (q L : ℕ) : Finset ℕ := (Finset.range L).filter (q ∣ ·)

def periodicCover (t k N : ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun j : Fin k ↦ multiplesBelow (modulus t j) (coverLength t k N)

lemma periodicCover_isAPCover (t k N : ℕ) :
    Green37.IsAPCover (periodicCover t k N : Set ℕ) N k := by
  rintro d ⟨hd, hdN⟩
  apply containsAP_of_mem hd
  intro j hj
  let jf : Fin k := ⟨j, hj⟩
  have hjle : j ≤ k := Nat.le_of_lt hj
  have hjd : j * d ≤ k * N := Nat.mul_le_mul hjle hdN
  have hlt : start t k d + j * d < coverLength t k N := by
    have ha := start_lt_period t k d
    simp only [coverLength]
    omega
  simp only [periodicCover, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
    multiplesBelow, Finset.mem_filter, Finset.mem_range]
  exact ⟨jf, hlt, modulus_dvd_start_add t k d jf⟩

lemma card_multiplesBelow_le (q L : ℕ) (hq : 0 < q) :
    (multiplesBelow q L).card ≤ L / q + 1 := by
  let T := (Finset.range (L / q + 1)).image (fun z ↦ q * z)
  have hsub : multiplesBelow q L ⊆ T := by
    intro x hx
    simp only [multiplesBelow, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨z, rfl⟩ := hx.2
    have hz : z ≤ L / q := by
      apply (Nat.le_div_iff_mul_le hq).2
      simpa [Nat.mul_comm] using Nat.le_of_lt hx.1
    simp only [T, Finset.mem_image, Finset.mem_range]
    exact ⟨z, by omega, rfl⟩
  calc
    (multiplesBelow q L).card ≤ T.card := Finset.card_le_card hsub
    _ ≤ (Finset.range (L / q + 1)).card := Finset.card_image_le
    _ = L / q + 1 := Finset.card_range _

lemma fermatNumber_le_modulus (t : ℕ) {k : ℕ} (j : Fin k) :
    Nat.fermatNumber t ≤ modulus t j := by
  exact Nat.fermatNumber_mono (Nat.le_add_right t j)

lemma card_periodicCover_le (t k N : ℕ) :
    (periodicCover t k N).card ≤
      k * (coverLength t k N / Nat.fermatNumber t + 1) := by
  calc
    (periodicCover t k N).card ≤
        ∑ j : Fin k, (multiplesBelow (modulus t j) (coverLength t k N)).card := by
      simpa [periodicCover] using
        (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin k)))
          (t := fun j ↦ multiplesBelow (modulus t j) (coverLength t k N)))
    _ ≤ ∑ _j : Fin k, (coverLength t k N / Nat.fermatNumber t + 1) := by
      apply Finset.sum_le_sum
      intro j _
      refine (card_multiplesBelow_le _ _ (modulus_pos t j)).trans ?_
      exact Nat.add_le_add_right
        (Nat.div_le_div_left (fermatNumber_le_modulus t j)
          (Nat.zero_lt_of_lt (Nat.two_lt_fermatNumber t))) 1
    _ = k * (coverLength t k N / Nat.fermatNumber t + 1) := by simp

lemma m_le_periodicCover_card (t k N : ℕ) :
    Green37.m N k ≤ (periodicCover t k N).card := by
  apply Nat.sInf_le
  exact ⟨periodicCover t k N, rfl, periodicCover_isAPCover t k N⟩

lemma periodicCover_card_real_le (t k N : ℕ) :
    ((periodicCover t k N).card : ℝ) ≤
      (k : ℝ) * ((coverLength t k N : ℝ) / Nat.fermatNumber t + 1) := by
  have h := card_periodicCover_le t k N
  calc
    ((periodicCover t k N).card : ℝ) ≤
        ((k * (coverLength t k N / Nat.fermatNumber t + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    _ = (k : ℝ) * (((coverLength t k N / Nat.fermatNumber t : ℕ) : ℝ) + 1) := by
      push_cast
      rfl
    _ ≤ (k : ℝ) * ((coverLength t k N : ℝ) / Nat.fermatNumber t + 1) := by
      gcongr
      exact Nat.cast_div_le

lemma m_real_le (t k N : ℕ) :
    (Green37.m N k : ℝ) ≤
      (k : ℝ) * ((coverLength t k N : ℝ) / Nat.fermatNumber t + 1) := by
  have hc : (Green37.m N k : ℝ) ≤ ((periodicCover t k N).card : ℝ) := by
    exact_mod_cast m_le_periodicCover_card t k N
  exact hc.trans (periodicCover_card_real_le t k N)

theorem m_isLittleO_id (k : ℕ) :
    (fun N ↦ (Green37.m N k : ℝ)) =o[atTop] (fun N ↦ (N : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hFtop : Tendsto (fun t ↦ (Nat.fermatNumber t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.fermatNumber_strictMono.tendsto_atTop
  obtain ⟨t, ht⟩ :=
    (tendsto_atTop.1 hFtop (2 * (k : ℝ) ^ 2 / c + 1)).exists
  have hFpos : (0 : ℝ) < Nat.fermatNumber t := by
    exact_mod_cast Nat.zero_lt_of_lt (Nat.two_lt_fermatNumber t)
  have ht' : 2 * (k : ℝ) ^ 2 / c < (Nat.fermatNumber t : ℝ) :=
    (lt_add_one _).trans_le ht
  have hnum : 2 * (k : ℝ) ^ 2 < (Nat.fermatNumber t : ℝ) * c :=
    (div_lt_iff₀ hc).mp ht'
  have hcoef : (k : ℝ) ^ 2 / Nat.fermatNumber t < c / 2 := by
    rw [div_lt_iff₀ hFpos]
    nlinarith [hnum]
  let C : ℝ := (k : ℝ) * ((period t k : ℝ) / Nat.fermatNumber t + 1)
  have hC : 0 ≤ C := by positivity
  filter_upwards [tendsto_atTop.1 tendsto_natCast_atTop_atTop (2 * C / c)] with N hN
  have hCN : C ≤ c / 2 * (N : ℝ) := by
    have := (div_le_iff₀ hc).mp hN
    nlinarith
  have hcoefN : (k : ℝ) ^ 2 / Nat.fermatNumber t * (N : ℝ) ≤
      c / 2 * (N : ℝ) := by
    gcongr
  have hm := m_real_le t k N
  have hdecomp :
      (k : ℝ) * ((coverLength t k N : ℝ) / Nat.fermatNumber t + 1) =
        C + (k : ℝ) ^ 2 / Nat.fermatNumber t * (N : ℝ) := by
    simp only [coverLength, C]
    push_cast
    field_simp
    ring
  rw [hdecomp] at hm
  have hfinal : (Green37.m N k : ℝ) ≤ c * (N : ℝ) := by
    calc
      (Green37.m N k : ℝ) ≤
          C + (k : ℝ) ^ 2 / Nat.fermatNumber t * (N : ℝ) := hm
      _ ≤ c / 2 * (N : ℝ) + c / 2 * (N : ℝ) := add_le_add hCN hcoefN
      _ = c * (N : ℝ) := by ring
  simpa [Real.norm_eq_abs, abs_of_nonneg] using hfinal

theorem m_isBigO_id (k : ℕ) :
    (fun N ↦ (Green37.m N k : ℝ)) =O[atTop] (fun N ↦ (N : ℝ)) :=
  (m_isLittleO_id k).isBigO

end

end Green37Proof

/-- `green_37_littleO` with the explicit answer `N ↦ N`. -/
theorem Green37.green_37_littleO_solved (k : ℕ) :
    (fun N ↦ (m N k : ℝ)) =o[atTop]
      (answer(fun N : ℕ ↦ (N : ℝ)) : ℕ → ℝ) :=
  Green37Proof.m_isLittleO_id k

/-- `green_37_bigO` with the same explicit answer `N ↦ N`. -/
theorem Green37.green_37_bigO_solved (k : ℕ) :
    (fun N ↦ (m N k : ℝ)) =O[atTop]
      (answer(fun N : ℕ ↦ (N : ℝ)) : ℕ → ℝ) :=
  Green37Proof.m_isBigO_id k

#check Green37.green_37_littleO_solved
#check Green37.green_37_bigO_solved
#print axioms Green37.green_37_littleO_solved
#print axioms Green37.green_37_bigO_solved
