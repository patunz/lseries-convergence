import Mathlib
import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound
import LSeriesConv.Analysis
import LSeriesConv.EulerAtPrime

/-!
# La serie L di una curva ellittica su `ℚ` converge per `Re s > 3/2`

Per ogni curva di Weierstrass `W` su `ℚ` la serie di Dirichlet dei coefficienti
di `W.LFunction` (la serie L di Mathlib) converge assolutamente nel semipiano
`Re s > 3/2`.

Ingredienti: la moltiplicatività della serie L e la forma del polinomio locale
in termini della traccia del Frobenius, con il limite di Hasse, da Tau Ceti; la
stima `|a_{p^k}| ≤ (k + 1) p^{k/2}` e un criterio di sommabilità per funzioni
moltiplicative, da `LSeriesConv.Analysis`.
-/

open IsDedekindDomain IsLocalRing NumberField Rat.HeightOneSpectrum PowerSeries

namespace LSeriesConv

section Locale

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] [Finite (ResidueField R)] (W : WeierstrassCurve K)

/-- **Stima dei coefficienti del fattore locale**: `|coeff k| ≤ (k + 1) q^{k/2}`,
con `q` l'ordine del campo residuo. Vale per ogni tipo di riduzione. -/
theorem norm_coeff_localPowerSeries_le (k : ℕ) :
    ‖((coeff k (W.localPowerSeries R) : ℤ) : ℂ)‖ ≤
      (k + 1) * √(Nat.card (ResidueField R) : ℝ) ^ k := by
  have hq1 : (1 : ℝ) ≤ √(Nat.card (ResidueField R) : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast Nat.card_pos
  have hc : constantCoeff ((W.localPolynomial R : Polynomial ℤ) : PowerSeries ℤ) =
      ((1 : ℤˣ) : ℤ) := by
    rw [WeierstrassCurve.localPolynomial]
    split_ifs <;> simp
  obtain ⟨α, β, hα, hβ, hP⟩ : ∃ α β : ℂ, ‖α‖ ≤ √(Nat.card (ResidueField R) : ℝ) ∧
      ‖β‖ ≤ √(Nat.card (ResidueField R) : ℝ) ∧
      ((W.localPolynomial R : Polynomial ℤ) : PowerSeries ℤ).map (Int.castRingHom ℂ) =
        (1 - C α * X) * (1 - C β * X) := by
    by_cases hg : (W.minimal R).HasGoodReduction R
    · obtain ⟨α, β, hα, hβ, hs, hp⟩ :=
        exists_roots (((W.minimal R).reduction R).frobeniusTrace_sq_le_four_mul_card)
      refine ⟨α, β, hα, hβ, ?_⟩
      rw [WeierstrassCurve.localPolynomial_eq_of_hasGoodReduction R W hg]
      simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_X, Polynomial.coe_pow, Polynomial.coe_one, map_add, map_sub, map_mul,
        map_pow, map_one, PowerSeries.map_C, PowerSeries.map_X]
      simp only [eq_intCast, Int.cast_natCast]
      rw [← hs, ← hp, map_add, map_mul]
      ring
    · rw [WeierstrassCurve.localPolynomial, if_neg hg]
      split_ifs
      · exact ⟨1, 0, by simpa using hq1, by simp, by simp⟩
      · exact ⟨-1, 0, by simpa using hq1, by simp, by simp⟩
      · exact ⟨0, 0, by simp, by simp, by simp⟩
  refine norm_coeff_le hα hβ ?_ k
  rw [← hP, ← map_mul, WeierstrassCurve.localPowerSeries, PowerSeries.invOfUnit_mul _ _ hc,
    map_one]

end Locale

/-- Il fattore locale della serie L in un posto finito, come serie di potenze.
Definito su un campo di numeri generico perché la struttura di algebra sul
completamento sia quella usata da Mathlib nella definizione della serie L. -/
noncomputable abbrev localSeries {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 K)) : PowerSeries ℤ :=
  (W.baseChange (v.adicCompletion K)).localPowerSeries (v.adicCompletionIntegers K)

lemma LFunction_eq_eulerProduct {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K) :
    W.LFunction = ArithmeticFunction.eulerProduct fun v : HeightOneSpectrum (𝓞 K) =>
      ArithmeticFunction.ofPowerSeries (Nat.card (ResidueField (v.adicCompletionIntegers K)))
        (localSeries W v) := rfl

lemma norm_coeff_localSeries_le {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 K)) [Finite (ResidueField (v.adicCompletionIntegers K))] (k : ℕ) :
    ‖((coeff k (localSeries W v) : ℤ) : ℂ)‖ ≤
      (k + 1) * √(Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) ^ k :=
  norm_coeff_localPowerSeries_le _ _ k

lemma constantCoeff_localSeries {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 K)) : constantCoeff (localSeries W v) = 1 :=
  WeierstrassCurve.constantCoeff_localPowerSeries _ _

section Posto

variable (v : HeightOneSpectrum (𝓞 ℚ))

instance : Fact (Nat.Prime (primesEquiv v : ℕ)) := ⟨(primesEquiv v).2⟩

/-- Il campo residuo del completamento di `ℚ` nel posto `v` è `ℤ/p`. -/
noncomputable def residueEquiv :
    ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (primesEquiv v : ℕ) :=
  (ResidueField.mapEquiv
    (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans PadicInt.residueField

lemma card_residueField :
    Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) = (primesEquiv v : ℕ) := by
  rw [Nat.card_congr (residueEquiv v).toEquiv, Nat.card_zmod]

lemma one_lt_card_residueField :
    1 < Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) := by
  rw [card_residueField]
  exact (primesEquiv v).2.one_lt

instance : Finite (ResidueField (v.adicCompletionIntegers ℚ)) :=
  Nat.finite_of_card_ne_zero (by have := one_lt_card_residueField v; omega)

end Posto

/-- Il posto di `ℚ` associato al primo `p`. -/
noncomputable def placeOfPrime {p : ℕ} (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  primesEquiv.symm ⟨p, hp⟩

lemma primesEquiv_placeOfPrime {p : ℕ} (hp : p.Prime) :
    (primesEquiv (placeOfPrime hp) : ℕ) = p :=
  congrArg Subtype.val (primesEquiv.apply_symm_apply ⟨p, hp⟩)

variable (W : WeierstrassCurve ℚ)

/-- Il coefficiente `p^k`-esimo della serie L è il coefficiente di `T^k` del
fattore locale in `p`. -/
theorem LFunction_apply_prime_pow_eq_coeff {p : ℕ} (hp : p.Prime) (k : ℕ) :
    W.LFunction (p ^ k) = coeff k (localSeries W (placeOfPrime hp)) := by
  let q : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun v =>
    Nat.card (ResidueField (v.adicCompletionIntegers ℚ))
  let f : HeightOneSpectrum (𝓞 ℚ) → PowerSeries ℤ := fun v => localSeries W v
  have hq : ∀ v, q v = (primesEquiv v : ℕ) := card_residueField
  have hqinj : Function.Injective q := by
    intro v w hvw
    rw [hq, hq] at hvw
    exact primesEquiv.injective (Subtype.ext hvw)
  have hf : ∀ v, constantCoeff (f v) = 1 := fun v => constantCoeff_localSeries W v
  set v₀ : HeightOneSpectrum (𝓞 ℚ) := placeOfPrime hp with hv₀def
  have hv₀ : (primesEquiv v₀ : ℕ) = p := primesEquiv_placeOfPrime hp
  have hne : ∀ v, v ≠ v₀ → ∀ m j, j ≠ 0 → q v ^ m ≠ p ^ j := by
    intro v hv m j hj hk
    apply hv
    have hqv : (q v).Prime := by rw [hq]; exact (primesEquiv v).2
    have hdvd : q v ∣ p := by
      rcases m with _ | m
      · rw [pow_zero] at hk
        exact absurd hk (Nat.one_lt_pow hj hp.one_lt).ne
      · have : q v ∣ p ^ j := by
          rw [← hk]
          exact dvd_pow_self _ (Nat.succ_ne_zero m)
        exact hqv.dvd_of_dvd_pow this
    have heq : (primesEquiv v : ℕ) = p := by
      rw [← hq]
      exact (Nat.prime_dvd_prime_iff_eq hqv hp).1 hdvd
    apply primesEquiv.injective
    apply Subtype.ext
    rw [heq, hv₀]
  have key := eulerProduct_apply_prime_pow q hqinj (fun v => one_lt_card_residueField v) f hf hp
    v₀ (by rw [hq, hv₀]) hne k
  rw [LFunction_eq_eulerProduct]
  exact key

/-- **Stima di Hasse sui coefficienti**: `|a_{p^k}| ≤ (k + 1) p^{k/2}`. -/
theorem norm_LFunction_prime_pow_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖((W.LFunction (p ^ k) : ℤ) : ℂ)‖ ≤ (k + 1) * √(p : ℝ) ^ k := by
  rw [LFunction_apply_prime_pow_eq_coeff W hp k]
  have := norm_coeff_localSeries_le W (placeOfPrime hp) k
  rwa [card_residueField, primesEquiv_placeOfPrime] at this

/-- **La serie L di una curva ellittica su `ℚ` converge assolutamente per
`Re s > 3/2`.** -/
theorem lseriesSummable_LFunction {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n => ((W.LFunction n : ℤ) : ℂ)) s := by
  set σ := s.re with hσ
  set F : ℕ → ℝ := fun n => ‖((W.LFunction n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-σ) with hF
  have hterm : ∀ n, ‖LSeries.term (fun n => ((W.LFunction n : ℤ) : ℂ)) s n‖ = F n := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · simp [hF, h0]
    · change _ / (n : ℝ) ^ s.re = _ * (n : ℝ) ^ (-s.re)
      rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  refine Summable.of_norm ((summable_congr hterm).2 ?_)
  have hmul := W.isMultiplicative_LFunction
  have he : 1 / 2 - σ < -1 := by linarith
  refine summable_of_multiplicative (G := fun n => tailConst * (n : ℝ) ^ (1 / 2 - σ))
    (fun n => by positivity) ?_ ?_ ?_ ?_ ?_ ?_
  · simp [hF, hmul.map_one]
  · intro m n hmn
    simp only [hF]
    rw [hmul.map_mul_of_coprime hmn, Int.cast_mul, norm_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  all_goals
    have hbound : ∀ {p : ℕ}, p.Prime →
        (0 ≤ (p : ℝ) ^ (1 / 2 - σ) ∧ (p : ℝ) ^ (1 / 2 - σ) ≤ 1 / 2) ∧
        ∀ k : ℕ, F (p ^ k) ≤ ((k : ℝ) + 1) * ((p : ℝ) ^ (1 / 2 - σ)) ^ k := by
      intro p hpp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      refine ⟨⟨by positivity, ?_⟩, fun k => ?_⟩
      · calc (p : ℝ) ^ (1 / 2 - σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) he.le
          _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
          _ ≤ 1 / 2 := by
              rw [one_div]
              exact inv_anti₀ (by norm_num) hp2
      · have h1 := norm_LFunction_prime_pow_le W hpp k
        have h2 : ((p ^ k : ℕ) : ℝ) ^ (-σ) = ((p : ℝ) ^ (-σ)) ^ k := by
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
            ← Real.rpow_mul hp0.le, mul_comm]
        have h3 : (p : ℝ) ^ (1 / 2 - σ) = √(p : ℝ) * (p : ℝ) ^ (-σ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp0]
          congr 1
        simp only [hF]
        rw [h2, h3, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · intro p hpp
    obtain ⟨⟨hy0, hy⟩, hb⟩ := hbound hpp
    exact (summable_and_tail_le hy0 hy (fun k => by positivity) hb).1
  · intro n
    exact mul_nonneg (tsum_nonneg fun k => by positivity) (by positivity)
  · exact (Real.summable_nat_rpow.2 he).mul_left _
  · intro p hpp
    obtain ⟨⟨hy0, hy⟩, hb⟩ := hbound hpp
    exact (summable_and_tail_le hy0 hy (fun k => by positivity) hb).2

end LSeriesConv

namespace LSeriesConv

/-- L'ascissa di convergenza assoluta della serie L è al più `3/2`. -/
theorem abscissaOfAbsConv_LFunction_le (W : WeierstrassCurve ℚ) :
    LSeries.abscissaOfAbsConv (fun n => ((W.LFunction n : ℤ) : ℂ)) ≤ (3 / 2 : ℝ) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    lseriesSummable_LFunction W (by simpa using hy)

end LSeriesConv
