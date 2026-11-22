module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# §B.5 Recurrence and equidistribution

Continuous-time torus equidistribution, vertical self-approximation, and recurrence of
reciprocal finite Euler products.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open Complex.HadamardThreeLines (verticalStrip)
open scoped ENNReal NNReal Topology

namespace RiemannMasullo

section Torus

variable {N : ℕ}

/-- Paper: Definition B.5.1.1(1), p. 626.
The product torus, represented by Mathlib's `UnitAddTorus (Fin N)`, is compact Hausdorff. -/
theorem unitAddTorus_compactHausdorff (N : ℕ) :
    CompactSpace (UnitAddTorus (Fin N)) ∧ T2Space (UnitAddTorus (Fin N)) := by sorry

/-- Paper: Definition B.5.1.1(2), p. 626.
The torus quotient reduces each real coordinate modulo one. -/
def torusQuotient (N : ℕ) : (Fin N → ℝ) →ₜ+ UnitAddTorus (Fin N) where
  toAddMonoidHom := AddMonoidHom.pi fun i ↦
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (Pi.evalAddMonoidHom _ i)
  continuous_toFun := continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_apply i)

/-- Two real vectors have the same image in the torus precisely when their coordinate
differences are integers. -/
theorem torusQuotient_eq_iff (x y : Fin N → ℝ) :
    torusQuotient N x = torusQuotient N y ↔ ∀ i, ∃ m : ℤ, x i - y i = (m : ℝ) := by sorry

/-- Paper: Definition B.5.1.1(2), p. 626.
The hitting times are the times in the given interval when the projected curve belongs
to the image of the target set modulo one. -/
def torusHittingTimes (γ : ℝ → Fin N → ℝ) (J : Set ℝ) (U : Set (Fin N → ℝ)) : Set ℝ :=
  J ∩ (torusQuotient N ∘ γ) ⁻¹' (torusQuotient N '' U)

/-- The constant zero curve hits a singleton integer vector modulo one at every time. -/
theorem torusHittingTimes_zero_singleton_int (J : Set ℝ) (m : Fin N → ℤ) :
    torusHittingTimes (fun _ ↦ 0) J {fun i ↦ (m i : ℝ)} = J := by sorry

/-- Paper: §B.5.1, p. 627.
The one-parameter torus subgroup of a frequency vector is the projection of its real line. -/
def torusFlow (τ : Fin N → ℝ) : ℝ →ₜ+ UnitAddTorus (Fin N) :=
  (torusQuotient N).comp (↑((ContinuousLinearMap.id ℝ ℝ).smulRight τ))

/-- At time one the flow has the phase given by the frequency vector modulo one. -/
theorem torusFlow_one (τ : Fin N → ℝ) : torusFlow τ 1 = torusQuotient N τ := by sorry

-- TODO(paper-gap): The sentence before §B.5.2 claims injectivity also in dimension one.
-- For N = 1 and τ₁ = 1, times zero and one have the same image.

section Kronecker

open Real UnitAddTorus

/-- Each exponential monomial is a character of the torus. -/
private theorem mFourier_add_apply (n : Fin N → ℤ) (x y : UnitAddTorus (Fin N)) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- Along the flow, an exponential monomial is the exponential of the paired frequency. -/
private theorem mFourier_torusFlow (τ : Fin N → ℝ) (n : Fin N → ℤ) (t : ℝ) :
    mFourier n (torusFlow τ t) =
      Complex.exp (2 * π * Complex.I * ((∑ i, (n i : ℝ) * τ i : ℝ) : ℂ) * t) := by
  have h (i : Fin N) : (torusFlow τ t) i = ((t * τ i : ℝ) : AddCircle (1 : ℝ)) := rfl
  simp only [mFourier, ContinuousMap.coe_mk, h, fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The time averages of a nonconstant imaginary exponential tend to zero. -/
private theorem tendsto_average_exp {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, Complex.exp (2 * π * Complex.I * c * t))
      atTop (𝓝 0) := by
  have ha : (2 * π * Complex.I * c : ℂ) ≠ 0 := by
    simp [hc, Real.pi_ne_zero, Complex.I_ne_zero]
  have hint (T : ℝ) : ∫ t in (0 : ℝ)..T, Complex.exp (2 * π * Complex.I * c * t) =
      (Complex.exp (2 * π * Complex.I * c * T) - 1) / (2 * π * Complex.I * c) := by
    rw [integral_exp_mul_complex ha]; simp
  have hb (T : ℝ) : ‖Complex.exp (2 * π * Complex.I * c * T) - 1‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (2 * π * Complex.I * c * T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (2 * π * Complex.I * c * T : ℂ) = ((2 * π * c * T : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I]
        norm_num
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using tendsto_inv_atTop_zero.const_mul (2 / ‖(2 * π * Complex.I * c : ℂ)‖))
  refine (eventually_gt_atTop 0).mono fun T hT ↦ ?_
  rw [hint, norm_mul, norm_div, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le,
    mul_comm]
  gcongr
  all_goals first
    | exact hb T
    | simp [abs_of_pos Real.pi_pos]

/-- Paper: §B.5.1, p. 627. Rationally independent frequencies give a dense
one-parameter subgroup of the ambient torus. -/
theorem torusFlow_denseRange_of_linearIndependent [NeZero N] {τ : Fin N → ℝ}
    (hτ : LinearIndependent ℚ τ) : DenseRange (torusFlow τ) := by
  -- Weyl's argument: time averages along the flow converge to the Haar integral, first for
  -- exponential monomials, then for all continuous functions by density and equicontinuity.
  classical
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨by simp [AddCircle.measure_univ]⟩
  let A : ℝ → C(UnitAddTorus (Fin N), ℂ) → ℂ :=
    fun T φ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, φ (torusFlow τ t)
  have hII (φ : C(UnitAddTorus (Fin N), ℂ)) (T : ℝ) :
      IntervalIntegrable (fun t ↦ φ (torusFlow τ t)) volume 0 T :=
    (φ.continuous.comp (torusFlow τ).continuous).intervalIntegrable _ _
  have hInt (φ : C(UnitAddTorus (Fin N), ℂ)) : Integrable φ :=
    integrableOn_univ.mp (φ.continuous.continuousOn.integrableOn_compact isCompact_univ)
  -- Nonzero integer vectors pair with the frequencies to a nonzero number.
  have hc (n : Fin N → ℤ) (hn : n ≠ 0) : (∑ i, (n i : ℝ) * τ i) ≠ 0 := by
    intro h
    apply hn
    have h0 := Fintype.linearIndependent_iff.mp hτ (fun i ↦ (n i : ℚ)) (by
      simpa [Rat.smul_def] using h)
    funext i
    exact_mod_cast h0 i
  -- Integrals of the monomials.
  have hint (n : Fin N → ℤ) : ∫ x, mFourier n x = if n = 0 then 1 else 0 := by
    split_ifs with hn
    · subst hn; simp [mFourier_zero]
    · set c := ∑ i, (n i : ℝ) * τ i
      have hw : mFourier n (torusFlow τ (1 / (2 * c))) = -1 := by
        rw [mFourier_torusFlow, show 2 * (π : ℂ) * Complex.I * (c : ℂ) * ((1 / (2 * c) : ℝ) : ℂ) =
          π * Complex.I by
          push_cast; field_simp [hc n hn]; exact div_self (Complex.ofReal_ne_zero.mpr (hc n hn))]
        exact Complex.exp_pi_mul_I
      have h1 := integral_add_right_eq_self (μ := volume) (fun x ↦ mFourier n x)
        (torusFlow τ (1 / (2 * c)))
      simp only [mFourier_add_apply, hw, integral_mul_const] at h1
      linear_combination (-1 / 2 : ℂ) * h1
  -- Averages of the monomials converge to their integrals.
  have hF (n : Fin N → ℤ) : Tendsto (fun T ↦ A T (mFourier n)) atTop (𝓝 (∫ x, mFourier n x)) := by
    rw [hint]
    split_ifs with hn
    · subst hn
      refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦ ?_)
      simp [A, mFourier_zero, hT]
    · simp only [A, mFourier_torusFlow]
      exact tendsto_average_exp (hc n hn)
  -- Linearity of the averages.
  have hAsub (T : ℝ) (φ ψ : C(UnitAddTorus (Fin N), ℂ)) : A T φ - A T ψ = A T (φ - ψ) := by
    simp only [A, ContinuousMap.sub_apply, intervalIntegral.integral_sub (hII φ T) (hII ψ T),
      mul_sub]
  have hAadd (T : ℝ) (φ ψ : C(UnitAddTorus (Fin N), ℂ)) : A T (φ + ψ) = A T φ + A T ψ := by
    simp only [A, ContinuousMap.add_apply, intervalIntegral.integral_add (hII φ T) (hII ψ T),
      mul_add]
  have hAsmul (T : ℝ) (a : ℂ) (φ : C(UnitAddTorus (Fin N), ℂ)) : A T (a • φ) = a * A T φ := by
    simp only [A, ContinuousMap.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
    ring
  -- The averages are uniformly 1-Lipschitz.
  have hAnorm (T : ℝ) (φ : C(UnitAddTorus (Fin N), ℂ)) : ‖A T φ‖ ≤ ‖φ‖ := by
    rcases eq_or_ne T 0 with rfl | hT
    · simp [A]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, φ (torusFlow τ t)‖ ≤ |T|⁻¹ * (‖φ‖ * |T - 0|) := by
          gcongr
          exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ φ.norm_coe_le_norm _
      _ = ‖φ‖ := by rw [sub_zero]; field_simp [abs_ne_zero.mpr hT]
  have hLip (T : ℝ) : LipschitzWith 1 (A T) := LipschitzWith.of_dist_le_mul fun φ ψ ↦ by
    rw [dist_eq_norm, dist_eq_norm, hAsub, NNReal.coe_one, one_mul]
    exact hAnorm T _
  have hIcont : Continuous fun φ : C(UnitAddTorus (Fin N), ℂ) ↦ ∫ x, φ x := by
    refine (LipschitzWith.of_dist_le_mul fun φ ψ ↦ ?_ : LipschitzWith 1 _).continuous
    rw [dist_eq_norm, dist_eq_norm, ← integral_sub (hInt φ) (hInt ψ), NNReal.coe_one, one_mul]
    calc ‖∫ x, (φ x - ψ x)‖ ≤ ‖φ - ψ‖ * (volume (univ : Set (UnitAddTorus (Fin N)))).toReal :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun x ↦
            (φ - ψ).norm_coe_le_norm x)
      _ = ‖φ - ψ‖ := by simp
  let V : Set C(UnitAddTorus (Fin N), ℂ) :=
    {φ | Tendsto (fun T ↦ A T φ) atTop (𝓝 (∫ x, φ x))}
  have hVclosed : IsClosed V :=
    ((LipschitzWith.uniformEquicontinuous A 1 hLip).equicontinuous).isClosed_setOfPred_tendsto
      hIcont
  have hspan : ((Submodule.span ℂ (range (mFourier (d := Fin N))) :
      Set C(UnitAddTorus (Fin N), ℂ))) ⊆ V := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨n, rfl⟩ := hx; exact hF n
    | zero => simp [V, A]
    | add φ ψ _ _ hφ hψ =>
      change Tendsto _ _ _
      simp only [hAadd, ContinuousMap.add_apply, integral_add (hInt φ) (hInt ψ)]
      exact hφ.add hψ
    | smul a φ _ hφ =>
      change Tendsto _ _ _
      simp only [hAsmul, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      exact hφ.const_mul a
  have hall (φ : C(UnitAddTorus (Fin N), ℂ)) : φ ∈ V := by
    have hmem : φ ∈ (Submodule.span ℂ (range (mFourier (d := Fin N)))).topologicalClosure := by
      rw [span_mFourier_closure_eq_top]; trivial
    exact closure_minimal hspan hVclosed hmem
  -- A bump function away from the orbit closure has zero averages but positive integral.
  by_contra hd
  obtain ⟨p, hp⟩ : ∃ p, p ∉ closure (range (torusFlow τ)) :=
    not_forall.mp fun h ↦ hd (dense_iff_closure_eq.mpr (eq_univ_of_forall h))
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed isClosed_closure
    isClosed_singleton (disjoint_singleton_right.mpr hp)
  let φ : C(UnitAddTorus (Fin N), ℂ) := ⟨fun x ↦ (f x : ℂ), by fun_prop⟩
  have hA (T : ℝ) : A T φ = 0 := by
    have : ∀ t, φ (torusFlow τ t) = 0 := fun t ↦ by
      change ((f (torusFlow τ t) : ℝ) : ℂ) = 0
      rw [hf0 (subset_closure (mem_range_self t))]
      simp
    simp [A, this]
  have hzero : ∫ x, φ x = 0 :=
    tendsto_nhds_unique (hall φ) (by simp only [hA]; exact tendsto_const_nhds)
  have hpos : 0 < ∫ x, f x :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (HasCompactSupport.of_compactSpace _) (fun x ↦ (hf01 x).1) (x := p)
      (by rw [hf1 rfl]; norm_num)
  have : ∫ x, φ x = ((∫ x, f x : ℝ) : ℂ) := integral_ofReal
  rw [this] at hzero
  exact hpos.ne' (Complex.ofReal_eq_zero.mp hzero)

end Kronecker

/-- Paper: §B.5.1, p. 627. For at least two rationally independent frequencies,
distinct times give distinct phases.
Deviation: Adds the dimension hypothesis used in the proof on p. 628. -/
theorem torusFlow_injective_of_linearIndependent (hN : 2 ≤ N) {τ : Fin N → ℝ}
    (hτ : LinearIndependent ℚ τ) : Injective (torusFlow τ) := by sorry

/-- Paper: Theorem B.5.2.1(1), p. 627.
The orbit closure is the closed additive subgroup obtained by closing the range of the flow. -/
def torusFlowClosure (τ : Fin N → ℝ) : AddSubgroup (UnitAddTorus (Fin N)) :=
  (torusFlow τ).toAddMonoidHom.range.topologicalClosure

/-- The zero frequency vector has the trivial orbit closure. -/
theorem torusFlowClosure_zero : torusFlowClosure (0 : Fin N → ℝ) = ⊥ := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627.
The torus flow takes values in its orbit closure when used in time averages. -/
def torusFlowInClosure (τ : Fin N → ℝ) (t : ℝ) : torusFlowClosure τ :=
  ⟨torusFlow τ t, AddSubgroup.le_topologicalClosure (torusFlow τ).toAddMonoidHom.range
    ⟨t, rfl⟩⟩

/-- In the ambient torus the restricted flow at time one gives the original phases. -/
theorem coe_torusFlowInClosure_one (τ : Fin N → ℝ) :
    (torusFlowInClosure τ 1 : UnitAddTorus (Fin N)) = torusQuotient N τ := by sorry

/-- Paper: §B.5.2.1, p. 627.
The fundamental domain for the torus quotient is the product of the half-open unit intervals. -/
def unitHalfOpenCube (N : ℕ) : Set (Fin N → ℝ) :=
  {x | ∀ i, x i ∈ Ico (0 : ℝ) 1}

/-- The one-dimensional cube includes the lower endpoint and excludes the upper endpoint. -/
theorem mem_unitHalfOpenCube_one (x : Fin 1 → ℝ) :
    x ∈ unitHalfOpenCube 1 ↔ 0 ≤ x 0 ∧ x 0 < 1 := by sorry

/-- Paper: §B.5.2.1, p. 627.
The torus volume is the pushforward of Lebesgue measure on the half-open unit cube. -/
theorem map_volume_unitHalfOpenCube (N : ℕ) :
    (volume.restrict (unitHalfOpenCube N)).map (torusQuotient N) =
      (volume : Measure (UnitAddTorus (Fin N))) := by sorry

/-- Paper: §B.5.2.1, p. 627.
Riemann integrability on a torus with Haar probability is expressed by boundedness and
continuity almost everywhere.
Deviation: Uses the Lebesgue criterion for Riemann integrability on the fundamental cube. -/
def TorusRiemannIntegrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (u : X → ℂ) : Prop :=
  (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) ∧ ∀ᵐ x ∂μ, ContinuousAt u x

/-- The indicator of the identity on the unit circle is Riemann integrable. -/
theorem torusRiemannIntegrable_indicator_zero :
    TorusRiemannIntegrable (volume : Measure UnitAddCircle)
      (({0} : Set UnitAddCircle).indicator (fun _ ↦ (1 : ℂ))) := by sorry

/-- Paper: Theorem B.5.2.1(1), p. 627.
The closed orbit subgroup is topologically isomorphic to the torus of dimension the rational
rank of the frequencies. -/
theorem torusFlowClosure_equiv_torus [NeZero N] (τ : Fin N → ℝ) :
    Nonempty (torusFlowClosure τ ≃ₜ+
      UnitAddTorus (Fin (Module.finrank ℚ (Submodule.span ℚ (range τ))))) := by sorry

-- TODO(paper-gap): Theorem B.5.2.1(2) for arbitrary Riemann-integrable observables.
-- A function supported on a Haar-null orbit arc can pull back to a nonmeasurable time function.
-- TODO(paper-gap): The bound in (B.5.2.14) needs an absolute value around the frequency.

/-- Paper: Theorem B.5.2.1(2), p. 627. Symmetric time averages of a
Riemann-integrable observable converge to its Haar probability integral.
Deviation: Requires Lebesgue measurability up to null sets along the orbit for the time integral. -/
theorem kroneckerWeyl_riemannIntegrable_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ) (hu : TorusRiemannIntegrable μ u)
    (ht : AEStronglyMeasurable (fun t ↦ u (torusFlowInClosure τ t)) volume) :
    Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627. Forward time averages of a
Riemann-integrable observable converge to its Haar probability integral.
Deviation: Requires Lebesgue measurability up to null sets on the forward orbit. -/
theorem kroneckerWeyl_riemannIntegrable_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ) (hu : TorusRiemannIntegrable μ u)
    (ht : AEStronglyMeasurable (fun t ↦ u (torusFlowInClosure τ t))
      (volume.restrict (Ici (0 : ℝ)))) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627.
Symmetric time averages of a continuous observable converge to its Haar probability integral.
Deviation: This is the continuous case singled out in the paper. -/
theorem kroneckerWeyl_continuous_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(torusFlowClosure τ, ℂ)) :
    Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627.
Forward time averages of a continuous observable converge to its Haar probability integral.
Deviation: This is the continuous case singled out in the paper. -/
theorem kroneckerWeyl_continuous_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(torusFlowClosure τ, ℂ)) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Lemma B.5.2.2, p. 627.
The indicator of an open set with null boundary can be sandwiched between continuous
functions into the unit interval whose integrated difference is arbitrarily small. -/
theorem exists_continuous_sandwich_indicator {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    {U : Set X} (hU : IsOpen U) (hfront : μ (frontier U) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ lower upper : C(X, Icc (0 : ℝ) 1),
      (∀ x, (lower x : ℝ) ≤ U.indicator (fun _ ↦ (1 : ℝ)) x ∧
        U.indicator (fun _ ↦ (1 : ℝ)) x ≤ (upper x : ℝ)) ∧
      (∫ x, ((upper x : ℝ) - (lower x : ℝ)) ∂μ) < ε := by sorry

-- TODO(paper-gap): Neither inclusion in the asserted frontier identity holds in general.
-- Away from the coordinate seams the cube projection is a local homeomorphism, so the
-- torus frontier lies in the image of the relative frontier together with the null seams.

/-- Paper: Remark B.5.2.3(1), p. 628.
A subset of the half-open cube with a null relative frontier has a torus image with null
frontier. The restricted Lebesgue measure identifies relative null sets via their images
in the ambient real vector space. -/
theorem volume_frontier_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (frontier (torusQuotient N '' (Subtype.val '' U))) = 0 := by sorry

/-- Paper: Remark B.5.2.3(2), p. 628.
For a Jordan-measurable subset of the cube, its torus image and the interior of that
image have the same volume. Jordan measurability is expressed by the null relative frontier. -/
theorem volume_interior_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (interior (torusQuotient N '' (Subtype.val '' U))) =
      volume (torusQuotient N '' (Subtype.val '' U)) := by sorry

/-- Paper: Remark B.5.2.3(2), p. 628.
The interior of the torus image of a Jordan-measurable set has null frontier. -/
theorem volume_frontier_interior_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (frontier (interior (torusQuotient N '' (Subtype.val '' U)))) = 0 := by sorry

/-- Paper: Corollary B.5.2.4, p. 631.
For a relatively open subset of the unit cube, the symmetric frequency of visits converges
to Haar probability on the orbit closure when the target has null relative frontier. -/
theorem torusHittingTimes_tendsto_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (unitHalfOpenCube N)) (hU : IsOpen U) :
    let V : Set (torusFlowClosure τ) := Subtype.val ⁻¹' (torusQuotient N '' (Subtype.val '' U))
    μ (frontier V) = 0 →
      Tendsto (fun T : ℝ ↦
        volume.real (torusHittingTimes (fun t ↦ t • τ) (Icc (-T) T) (Subtype.val '' U)) /
          (2 * T)) atTop (𝓝 (μ.real V)) := by sorry

/-- Paper: Corollary B.5.2.4, p. 631.
For a relatively open subset of the unit cube, the forward frequency of visits converges
to Haar probability on the orbit closure when the target has null relative frontier. -/
theorem torusHittingTimes_tendsto_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (unitHalfOpenCube N)) (hU : IsOpen U) :
    let V : Set (torusFlowClosure τ) := Subtype.val ⁻¹' (torusQuotient N '' (Subtype.val '' U))
    μ (frontier V) = 0 →
      Tendsto (fun T : ℝ ↦
        volume.real (torusHittingTimes (fun t ↦ t • τ) (Icc 0 T) (Subtype.val '' U)) /
          T) atTop (𝓝 (μ.real V)) := by sorry

-- TODO(paper-gap): Remark B.5.2.5 does not state the discrete versions. The discrete orbit
-- closure can be disconnected, so the continuous-time dimension claim cannot be reused verbatim.

end Torus

section Recurrence

/-- Paper: Definition B.5.3.1(1), p. 632.
The upper density is the limsup of the fraction of a symmetric interval occupied by the set.
Deviation: For arbitrary subsets the numerator is Lebesgue outer measure. -/
def upperDensity (X : Set ℝ) : ℝ :=
  limsup (fun T : ℝ ↦ volume.real (Icc (-T) T ∩ X) / (2 * T)) atTop

/-- Every right half-line has symmetric upper density one half. -/
theorem upperDensity_Ici (a : ℝ) : upperDensity (Ici a) = 1 / 2 := by sorry

/-- Paper: Definition B.5.3.1(2), p. 632.
The vertical return times are the shifts whose uniform approximation error on the specified set
is less than the tolerance. -/
def verticalReturnTimes (f : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {t | (⨆ z : K, (‖f ((z : ℂ) + (t : ℂ) * Complex.I) - f z‖₊ : ℝ≥0∞)) < ENNReal.ofReal ε}

/-- The return times of the identity on a singleton are the shifts of absolute value
less than the tolerance. -/
theorem verticalReturnTimes_id_singleton (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    verticalReturnTimes id {z} ε = Ioo (-ε) ε := by sorry

/-- Paper: Definition B.5.3.1(2), p. 632.
Strong recurrence means positive upper density of vertical return times for every positive
tolerance.
Deviation: The domain is represented by a complex function with holomorphy on the strip
and compact containment imposed at use sites. The printed `C_{>R}` is read as `C_I`. -/
def StronglyRecurrentOn (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ ε > 0, 0 < upperDensity (verticalReturnTimes f K ε)

/-- On compact sets, the complex exponential is strongly recurrent by its imaginary period. -/
theorem stronglyRecurrentOn_exp {K : Set ℂ} (hK : IsCompact K) :
    StronglyRecurrentOn Complex.exp K := by sorry

-- TODO(paper-gap): Proposition B.5.3.2 forces T₀ = 0. Over ℚ with the trivial character
-- and a finite place above 2, the denominator at T₀ vanishes.

open IsDedekindDomain NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- Paper: Proposition B.5.3.3, p. 632.
The reciprocal partial Euler product multiplies the reciprocals of the finite Euler factors
from §3.2. At a zero of the local Euler polynomial this gives its holomorphic value zero. -/
def reciprocalPartialHeckeEulerProduct (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  ∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹

/-- For a singleton unramified place the product is the linear factor with coefficient
given by the value of the character on a local uniformizer. -/
theorem reciprocalPartialHeckeEulerProduct_singleton
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (s : ℂ) :
    reciprocalPartialHeckeEulerProduct χ {v} s =
      1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s) := by
  classical
  simp [reciprocalPartialHeckeEulerProduct, finiteHeckeEulerFactor, hv]

/-- Paper: Proposition B.5.3.2, p. 632. There is a nondecreasing sequence
escaping to infinity on both tails on which the reciprocal product is bounded away from zero.
Deviation: Uses the negative sign condition for strictly negative indices. The height at
index zero may then be chosen away from all poles of the Euler factors. -/
theorem exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧ Monotone T ∧
      (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
      Tendsto (fun k ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop ∧
      ∀ k, c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((T k : ℂ) * Complex.I)‖ := by sorry

/-- Paper: Proposition B.5.3.3, p. 632.
The nonnegative vertical shifts that uniformly approximate the reciprocal partial Euler
product on the compact set have positive symmetric upper density. -/
theorem reciprocalPartialHeckeEulerProduct_upperDensity_nonneg
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {a b : ℝ} (hI : (0 : ℝ) ∈ Ioo a b) {K : Set ℂ} (hK : IsCompact K)
    (hKI : K ⊆ verticalStrip a b) (hKint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    0 < upperDensity (Ici 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) :=
  by sorry

/-- Paper: Proposition B.5.3.3, p. 632.
The nonpositive vertical shifts that uniformly approximate the reciprocal partial Euler
product on the compact set have positive symmetric upper density. -/
theorem reciprocalPartialHeckeEulerProduct_upperDensity_nonpos
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {a b : ℝ} (hI : (0 : ℝ) ∈ Ioo a b) {K : Set ℂ} (hK : IsCompact K)
    (hKI : K ⊆ verticalStrip a b) (hKint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    0 < upperDensity (Iic 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) :=
  by sorry

-- TODO(paper-gap): The proof of Proposition B.5.3.3 uses the ambient cube to infer Haar
-- nullity on a possibly lower-dimensional orbit closure. The level set must be treated
-- intrinsically on that closure. To apply the area estimate, integrate on an open
-- neighbourhood of the target compact set.

/-- Paper: Lemma B.5.3.4(1), p. 633.
For a holomorphic function on a bounded open strip, strong recurrence on a compact subset
descends to every compact subset of that subset. -/
theorem stronglyRecurrentOn_of_subset {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) {K K' : Set ℂ}
    (hK : IsCompact K) (hKI : K ⊆ verticalStrip a b) (hK' : IsCompact K') (hsub : K' ⊆ K)
    (hrec : StronglyRecurrentOn f K) : StronglyRecurrentOn f K' := by sorry

-- TODO(paper-gap): Lemma B.5.3.4(2) fails. A compact vertical segment need not fit inside
-- any disc contained in the strip, and disc-by-disc recurrence need not give simultaneous return
-- times on that segment. The report gives a Runge approximation counterexample.

/-- Paper: Lemma B.5.3.5, p. 633.
If the squared area error integrated over the closure of the open set is below
`π * δ² * X²`, the uniform error on the compact set is below `X`.
Deviation: The subscript `r` in (B.5.3.6) is read as `2`, as in (B.5.3.8). -/
theorem areaApproximation_subset_verticalReturnTimes {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) {K U : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hKI : K ⊆ verticalStrip a b)
    (hU : IsOpen U) (hUcompact : IsCompact (closure U)) (hUI : closure U ⊆ verticalStrip a b)
    (hKU : K ⊆ U) {δ : ℝ} (hδ : δ = ⨅ z : K, Metric.infDist (z : ℂ) Uᶜ)
    (hδpos : 0 < δ) {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    {t ∈ Icc (-T) T | (∫ z in closure U, ‖f (z + (t : ℂ) * Complex.I) - f z‖ ^ 2) <
      Real.pi * δ ^ 2 * X ^ 2} ⊆ Icc (-T) T ∩ verticalReturnTimes f K X := by sorry

end Recurrence

end RiemannMasullo
