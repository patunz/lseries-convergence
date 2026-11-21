import Mathlib

/-!
# Il prodotto di Eulero valutato in un primo

Se i fattori locali sono serie di potenze in `qᵢ⁻ˢ` con termine costante 1 e
i `qᵢ` sono distinti, il coefficiente `p`-esimo del prodotto di Eulero è il
coefficiente di `T` del fattore con `qᵢ = p`.
-/

open ArithmeticFunction Filter

namespace LSeriesConv

variable {ι : Type*}

lemma finsetProd_apply_one (g : ι → ArithmeticFunction ℤ) (hg : ∀ i, g i 1 = 1)
    (s : Finset ι) : (∏ i ∈ s, g i) 1 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, mul_apply_one, hg, ih, mul_one]

lemma finsetProd_apply_prime (g : ι → ArithmeticFunction ℤ) (hg : ∀ i, g i 1 = 1)
    {p : ℕ} (hp : p.Prime) (s : Finset ι) : (∏ i ∈ s, g i) p = ∑ i ∈ s, g i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_apply_ne hp.one_lt.ne']
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun i j => g a i * (∏ i ∈ s, g i) j), hp.divisors,
      Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos, hg, one_mul, ih,
      finsetProd_apply_one g hg, mul_one, add_comm]

/-- Il coefficiente `p`-esimo di un prodotto di Eulero. -/
theorem eulerProduct_apply_prime (q : ι → ℕ) (hq : Function.Injective q)
    (hq1 : ∀ i, 1 < q i) (f : ι → PowerSeries ℤ) (hf : ∀ i, (f i).constantCoeff = 1)
    {p : ℕ} (hp : p.Prime) (i₀ : ι) (hi₀ : q i₀ = p)
    (hne : ∀ i, i ≠ i₀ → ∀ k, q i ^ k ≠ p) :
    eulerProduct (fun i ↦ ofPowerSeries (q i) (f i)) p = (f i₀).coeff 1 := by
  have : Northcott q := ⟨fun b => (Set.finite_Iic b).preimage hq.injOn⟩
  have h1 := tendsTo_eulerProduct_ofPowerSeries q f hf p
  obtain ⟨s, hs, hi⟩ := (h1.and (eventually_ge_atTop {i₀})).exists
  rw [← hs, finsetProd_apply_prime _ (fun i => by simp [hf]) hp, Finset.sum_eq_single i₀]
  · have := ofPowerSeries_apply_pow (hq1 i₀) (f i₀) 1
    rw [pow_one] at this
    rw [← hi₀]
    exact this
  · intro i _ hi'
    rw [ofPowerSeries_apply (hq1 i),
      Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ => hne i hi' k hk)]
    rfl
  · intro h
    exact absurd (hi (Finset.mem_singleton_self _)) h

/-! ## Potenze di un primo -/

/-- Una funzione aritmetica che vale `1` in `1` e `0` sulle potenze positive di `p`. -/
def TrivialAt (p : ℕ) (h : ArithmeticFunction ℤ) : Prop :=
  h 1 = 1 ∧ ∀ j, j ≠ 0 → h (p ^ j) = 0

/-- Moltiplicare per una funzione banale in `p` non cambia i valori sulle potenze di `p`. -/
lemma mul_apply_prime_pow {p : ℕ} (hp : p.Prime) (g h : ArithmeticFunction ℤ)
    (hh : TrivialAt p h) (k : ℕ) : (g * h) (p ^ k) = g (p ^ k) := by
  rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (p ^ k, 1)]
  · rw [hh.1, mul_one]
  · rintro ⟨d, e⟩ hde hne
    rw [Nat.mem_divisorsAntidiagonal] at hde
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left d hde.1)
    by_cases hj0 : j = 0
    · exfalso
      apply hne
      have hd : d = p ^ k := by simpa [hj0] using hde.1
      rw [hd, hj0, pow_zero]
    · change g d * h (p ^ j) = 0
      rw [hh.2 j hj0, mul_zero]
  · intro hnot
    exfalso
    apply hnot
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨mul_one _, pow_ne_zero _ hp.ne_zero⟩

lemma TrivialAt.one {p : ℕ} (hp : p.Prime) : TrivialAt p 1 :=
  ⟨one_one, fun _ hj => one_apply_ne (Nat.one_lt_pow hj hp.one_lt).ne'⟩

lemma TrivialAt.mul {p : ℕ} (hp : p.Prime) {g h : ArithmeticFunction ℤ} (hg : TrivialAt p g)
    (hh : TrivialAt p h) : TrivialAt p (g * h) :=
  ⟨by rw [mul_apply_one, hg.1, hh.1, mul_one],
    fun j hj => by rw [mul_apply_prime_pow hp g h hh, hg.2 j hj]⟩

lemma finsetProd_trivialAt {p : ℕ} (hp : p.Prime) (g : ι → ArithmeticFunction ℤ) (s : Finset ι)
    (h : ∀ i ∈ s, TrivialAt p (g i)) : TrivialAt p (∏ i ∈ s, g i) :=
  Finset.prod_induction _ (TrivialAt p) (fun _ _ => TrivialAt.mul hp) (TrivialAt.one hp) h

/-- Il coefficiente `p^k`-esimo di un prodotto di Eulero è il coefficiente di
`T^k` del fattore in `p`. -/
theorem eulerProduct_apply_prime_pow (q : ι → ℕ) (hq : Function.Injective q)
    (hq1 : ∀ i, 1 < q i) (f : ι → PowerSeries ℤ) (hf : ∀ i, (f i).constantCoeff = 1)
    {p : ℕ} (hp : p.Prime) (i₀ : ι) (hi₀ : q i₀ = p)
    (hne : ∀ i, i ≠ i₀ → ∀ m j, j ≠ 0 → q i ^ m ≠ p ^ j) (k : ℕ) :
    eulerProduct (fun i ↦ ofPowerSeries (q i) (f i)) (p ^ k) = (f i₀).coeff k := by
  classical
  have : Northcott q := ⟨fun b => (Set.finite_Iic b).preimage hq.injOn⟩
  have h1 := tendsTo_eulerProduct_ofPowerSeries q f hf (p ^ k)
  obtain ⟨s, hs, hi⟩ := (h1.and (eventually_ge_atTop {i₀})).exists
  have hmem : i₀ ∈ s := hi (Finset.mem_singleton_self _)
  have htriv : TrivialAt p (∏ i ∈ s.erase i₀, ofPowerSeries (q i) (f i)) := by
    apply finsetProd_trivialAt hp
    intro i hi'
    have hii : i ≠ i₀ := Finset.ne_of_mem_erase hi'
    refine ⟨by simp [hf], fun j hj => ?_⟩
    rw [ofPowerSeries_apply (hq1 i),
      Function.extend_apply' _ _ _ (fun ⟨m, hm⟩ => hne i hii m j hj hm)]
    rfl
  rw [← hs, ← Finset.mul_prod_erase s _ hmem, mul_apply_prime_pow hp _ _ htriv, ← hi₀]
  exact ofPowerSeries_apply_pow (hq1 i₀) (f i₀) k

end LSeriesConv
