import Mathlib

/-!
# Due strumenti analitici

* `norm_coeff_le`: se una serie di potenze intera `f` è l'inversa di
  `(1 - αT)(1 - βT)` con `‖α‖, ‖β‖ ≤ r`, allora `|coeff k f| ≤ (k + 1) r ^ k`.
* `summable_of_multiplicative`: una funzione moltiplicativa a valori reali non
  negativi è sommabile se le somme sulle potenze positive di ogni primo sono
  dominate da una funzione sommabile.

Dipendono solo da Mathlib.
-/

open PowerSeries

namespace LSeriesConv

/-- La serie geometrica è l'inversa di `1 - αT`. -/
lemma mk_pow_mul_one_sub (α : ℂ) :
    (PowerSeries.mk fun k => α ^ k) * (1 - C α * X) = 1 := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_mul_X, coeff_mul_C, coeff_mk, coeff_mk, coeff_one,
      if_neg (Nat.succ_ne_zero n), pow_succ, sub_self]

/-- **Stima dei coefficienti locali.** -/
theorem norm_coeff_le {α β : ℂ} {r : ℝ} (hα : ‖α‖ ≤ r) (hβ : ‖β‖ ≤ r) {f : PowerSeries ℤ}
    (hf : f.map (Int.castRingHom ℂ) * ((1 - C α * X) * (1 - C β * X)) = 1) (k : ℕ) :
    ‖((coeff k f : ℤ) : ℂ)‖ ≤ (k + 1) * r ^ k := by
  have hr : 0 ≤ r := (norm_nonneg α).trans hα
  set g : PowerSeries ℂ := (PowerSeries.mk fun k => α ^ k) * (PowerSeries.mk fun k => β ^ k)
    with hg
  have hgP : g * ((1 - C α * X) * (1 - C β * X)) = 1 := by
    calc g * ((1 - C α * X) * (1 - C β * X))
        = ((PowerSeries.mk fun k => α ^ k) * (1 - C α * X)) *
            ((PowerSeries.mk fun k => β ^ k) * (1 - C β * X)) := by rw [hg]; ring
      _ = 1 := by rw [mk_pow_mul_one_sub, mk_pow_mul_one_sub, mul_one]
  have hfg : f.map (Int.castRingHom ℂ) = g := by
    calc f.map (Int.castRingHom ℂ)
        = f.map (Int.castRingHom ℂ) * (g * ((1 - C α * X) * (1 - C β * X))) := by
          rw [hgP, mul_one]
      _ = (f.map (Int.castRingHom ℂ) * ((1 - C α * X) * (1 - C β * X))) * g := by ring
      _ = g := by rw [hf, one_mul]
  have hcoeff : ((coeff k f : ℤ) : ℂ) = coeff k g := by
    rw [← hfg, coeff_map]
    rfl
  rw [hcoeff, hg, coeff_mul]
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, coeff p.1 (PowerSeries.mk fun k => α ^ k) *
          coeff p.2 (PowerSeries.mk fun k => β ^ k)‖
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, r ^ k := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
        rw [coeff_mk, coeff_mk, norm_mul, norm_pow, norm_pow,
          ← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, pow_add]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hα _)
          (pow_le_pow_left₀ (norm_nonneg _) hβ _) (pow_nonneg (norm_nonneg _) _)
          (pow_nonneg hr _)
    _ = (k + 1) * r ^ k := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        push_cast
        ring

/-- Se `a² ≤ 4q`, il polinomio `1 - aT + qT²` si spezza su `ℂ` con radici inverse
di modulo al più `√q`. -/
lemma exists_roots {a : ℤ} {q : ℕ} (h : a ^ 2 ≤ 4 * q) :
    ∃ α β : ℂ, ‖α‖ ≤ √q ∧ ‖β‖ ≤ √q ∧ α + β = a ∧ α * β = q := by
  have hD : (0 : ℝ) ≤ 4 * q - (a : ℝ) ^ 2 := by
    have : ((a ^ 2 : ℤ) : ℝ) ≤ ((4 * q : ℤ) : ℝ) := Int.cast_le.2 h
    push_cast at this
    linarith
  set d : ℝ := √(4 * q - (a : ℝ) ^ 2) with hd
  have hdd : d * d = 4 * q - (a : ℝ) ^ 2 := Real.mul_self_sqrt hD
  have hn : ∀ e : ℝ, e * e = d * d → ‖(⟨a / 2, e / 2⟩ : ℂ)‖ ≤ √q := by
    intro e he
    refine Real.le_sqrt_of_sq_le ?_
    rw [Complex.sq_norm, Complex.normSq_mk]
    nlinarith
  refine ⟨⟨a / 2, d / 2⟩, ⟨a / 2, -d / 2⟩, hn d rfl, ?_, ?_, ?_⟩
  · exact hn (-d) (by ring)
  · apply Complex.ext
    · simp only [Complex.add_re, Complex.intCast_re]
      ring
    · simp only [Complex.add_im, Complex.intCast_im]
      ring
  · apply Complex.ext
    · simp only [Complex.mul_re, Complex.natCast_re]
      nlinarith
    · simp only [Complex.mul_im, Complex.natCast_im]
      ring

/-- La costante `∑ (k + 2) / 2 ^ k`. -/
noncomputable def tailConst : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) * (1 / 2) ^ k

lemma summable_tailConst : Summable fun k : ℕ => ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k := by
  have h1 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * (1 / 2 : ℝ) ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have h2 : Summable fun k : ℕ => (2 : ℝ) * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
  refine (h1.add h2).congr fun k => ?_
  ring

/-- Una successione dominata da `(k + 1) y ^ k` con `0 ≤ y ≤ 1/2` è sommabile e
la sua coda da `1` in poi è al più `tailConst * y`. -/
lemma summable_and_tail_le {u : ℕ → ℝ} {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2)
    (hu0 : ∀ k, 0 ≤ u k) (hu : ∀ k, u k ≤ (k + 1) * y ^ k) :
    Summable u ∧ ∑' k, u (k + 1) ≤ tailConst * y := by
  have hdom : ∀ k, u (k + 1) ≤ y * (((k : ℝ) + 2) * (1 / 2) ^ k) := by
    intro k
    refine (hu (k + 1)).trans ?_
    have hpow : y ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hy0 hy k
    have hk : (0 : ℝ) ≤ (k : ℝ) + 2 := by positivity
    calc ((k + 1 : ℕ) + 1 : ℝ) * y ^ (k + 1) = y * (((k : ℝ) + 2) * y ^ k) := by
          push_cast
          ring
      _ ≤ y * (((k : ℝ) + 2) * (1 / 2) ^ k) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hk) hy0
  have hsum' : Summable fun k => u (k + 1) :=
    Summable.of_nonneg_of_le (fun k => hu0 _) hdom (summable_tailConst.mul_left y)
  refine ⟨(summable_nat_add_iff 1).1 hsum', ?_⟩
  calc ∑' k, u (k + 1) ≤ ∑' k : ℕ, y * (((k : ℝ) + 2) * (1 / 2) ^ k) :=
        hsum'.tsum_le_tsum hdom (summable_tailConst.mul_left y)
    _ = tailConst * y := by rw [tsum_mul_left, tailConst, mul_comm]

/-- **Criterio di sommabilità per funzioni moltiplicative.** -/
theorem summable_of_multiplicative {F G : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n) (hF1 : F 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n)
    (hp : ∀ {p : ℕ}, p.Prime → Summable fun k => F (p ^ k))
    (hG0 : ∀ n, 0 ≤ G n) (hG : Summable G)
    (hFG : ∀ {p : ℕ}, p.Prime → ∑' k, F (p ^ (k + 1)) ≤ G p) : Summable F := by
  refine summable_of_sum_le hF0 (c := F 0 + Real.exp (∑' n, G n)) fun t => ?_
  set N := t.sup id + 1 with hN
  set s : Finset ℕ := N.primesBelow with hs
  have hnorm : ∀ {p : ℕ}, p.Prime → Summable fun k => ‖F (p ^ k)‖ := fun {p} hpp =>
    (hp hpp).congr fun k => (Real.norm_of_nonneg (hF0 _)).symm
  obtain ⟨hsumm, hhas⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hF1 hmul hnorm s
  have hsumm' : Summable fun m : Nat.factoredNumbers s => F m :=
    hsumm.congr fun m => Real.norm_of_nonneg (hF0 _)
  have hind : Summable ((Nat.factoredNumbers s).indicator F) :=
    summable_subtype_iff_indicator.1 hsumm'
  have hprod : ∏ p ∈ s with p.Prime, ∑' n, F (p ^ n) ≤ Real.exp (∑' n, G n) := by
    calc ∏ p ∈ s with p.Prime, ∑' n, F (p ^ n)
        ≤ ∏ p ∈ s with p.Prime, Real.exp (G p) := by
          gcongr with p hpm
          · exact fun p _ => tsum_nonneg fun n => hF0 _
          have hpp : p.Prime := (Finset.mem_filter.1 hpm).2
          rw [(hp hpp).tsum_eq_zero_add, pow_zero, hF1]
          calc 1 + ∑' k, F (p ^ (k + 1)) ≤ 1 + G p := by linarith [hFG hpp]
            _ ≤ Real.exp (G p) := by linarith [Real.add_one_le_exp (G p)]
      _ = Real.exp (∑ p ∈ s with p.Prime, G p) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' n, G n) :=
          Real.exp_le_exp.2 (hG.sum_le_tsum _ fun n _ => hG0 n)
  have hle : ∀ n ∈ t, F n ≤ (if n = 0 then F 0 else 0) + (Nat.factoredNumbers s).indicator F n := by
    intro n hn
    by_cases h0 : n = 0
    · subst h0
      simp only [↓reduceIte]
      exact le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ => hF0 _) _)
    · have hmem : n ∈ Nat.factoredNumbers s := by
        refine ⟨h0, fun p hpn => ?_⟩
        have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hpn
        have hpl : p ≤ n := Nat.le_of_mem_primeFactorsList hpn
        have hnl : n ≤ t.sup id := Finset.le_sup (f := id) hn
        rw [hs, Nat.mem_primesBelow]
        exact ⟨by omega, hpp⟩
      simp only [h0, ↓reduceIte, zero_add, Set.indicator_of_mem hmem, le_refl]
  calc ∑ n ∈ t, F n
      ≤ ∑ n ∈ t, ((if n = 0 then F 0 else 0) + (Nat.factoredNumbers s).indicator F n) :=
        Finset.sum_le_sum hle
    _ = (∑ n ∈ t, if n = 0 then F 0 else 0) + ∑ n ∈ t, (Nat.factoredNumbers s).indicator F n :=
        Finset.sum_add_distrib
    _ ≤ F 0 + ∑' n, (Nat.factoredNumbers s).indicator F n := by
        refine add_le_add ?_ (hind.sum_le_tsum _ fun n _ =>
          Set.indicator_nonneg (fun _ _ => hF0 _) _)
        rw [Finset.sum_ite_eq']
        split_ifs
        · exact le_rfl
        · exact hF0 0
    _ = F 0 + ∏ p ∈ s with p.Prime, ∑' n, F (p ^ n) := by
        rw [← tsum_subtype, hhas.tsum_eq]
    _ ≤ F 0 + Real.exp (∑' n, G n) := by linarith

end LSeriesConv
