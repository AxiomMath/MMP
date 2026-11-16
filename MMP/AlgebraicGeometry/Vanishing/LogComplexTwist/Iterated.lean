module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.Composition
public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.Inclusion
public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartExactness

/-!
# Iterated twists of the fractional logarithmic complex

Let `π : V ⟶ Spec ℂ` be smooth with `V` integral, `D` a reduced relative simple normal crossing
divisor, and `C^•` the fractional logarithmic complex `𝒪_V(-M) · Ω^•_V(log D)` of an `N`-th root
`𝒪_V(M)` of `𝒪_V(Bn)` through `N M = Bn + div ψ`, with `Bn ≥ 0` of support `D`. For every
`k ≥ 0` the twist `C^•(-kD)`, the fractional logarithmic complex of `M + kD`, maps to `C^•` by the
inclusion of forms, and this inclusion is a quasi-isomorphism.

The twist by `kD` is reached one component at a time: from `M + A` to `M + A + E` for a component
`E` of `D`, the complex of `M + A + E` has a model, the inclusion of forms is a morphism of
complexes which is a monomorphism in every degree, and it is relatively locally exact because the
residue `(Bn + N A)(E)/N` of the connection along `E` is nonzero. Composites of such inclusions
are again relatively locally exact inclusions, and relative local exactness of a monomorphism gives
a quasi-isomorphism.

## Main definitions

* `MMP.LcBpf.Reach`: the twist `C^•(-A)` has a model mapping to `C^•` by a relatively locally
  exact inclusion of forms which is a monomorphism in every degree.

## Main results

* `MMP.LcBpf.reach_add_single`: if `C^•(-A)` is reached, so is `C^•(-(A + E))` for a component
  `E` of `D`.
* `MMP.LcBpf.reach_nsmul`: the twist `C^•(-kD)` is reached for every `k`.

## References

* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof

/-- If a section `x` over `W` maps to the rational function `φ`, then so does its restriction to
any open `W' ≤ W`. -/
theorem toRationalFunctionsPresheaf_restrict {X : Scheme} {W W' : X.Opens} (h : W' ≤ W)
    (x : Γ(X, W)) (φ : RationalFunctions X)
    (hx : (toRationalFunctionsPresheaf X).app (op W) x = ratRes W φ) :
    (toRationalFunctionsPresheaf X).app (op W') (X.presheaf.map (homOfLE h).op x) =
      ratRes W' φ := by
  rw [toRationalFunctionsPresheaf_app_map, hx]
  rfl

/-- A sum `f + n • g` of nonnegative integer-valued functions is nonnegative. -/
theorem add_natCast_smul_apply_nonneg {α : Type*} {f g : α →₀ ℤ} (n : ℕ) (hf : ∀ a, 0 ≤ f a)
    (hg : ∀ a, 0 ≤ g a) (a : α) : 0 ≤ (f + (n : ℤ) • g) a := by
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have := hf a
  have := mul_nonneg (Int.natCast_nonneg n) (hg a)
  omega

/-- For nonnegative `f, g` with `g` vanishing where `f` does, `f + n • g` vanishes exactly where
`f` does. -/
theorem add_natCast_smul_apply_eq_zero_iff {α : Type*} {f g : α →₀ ℤ} (n : ℕ)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (hgf : ∀ a, f a = 0 → g a = 0) (a : α) :
    (f + (n : ℤ) • g) a = 0 ↔ f a = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, hgf a h]⟩
  have := hf a
  have := mul_nonneg (Int.natCast_nonneg n) (hg a)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h
  omega

/-- The support of a component `E` of `D` lies in the support of `D`. -/
theorem supp_single_le_supp {X : Scheme} {D : Divisor X} {E : MMP.Mori.PrimeDivisor X}
    (hE : E ∈ D.support) :
    DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ) : Divisor X) ≤ D.supp := by
  classical
  intro x hx
  obtain ⟨E', hE', hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  obtain rfl : E' = E := by
    by_contra hne
    apply hE'
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    rw [if_neg (fun h => hne h.symm)]
  exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E', Finsupp.mem_support_iff.1 hE, hxE⟩

section Iteration

variable (d : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension d π]
  [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
  (D : Divisor V) (hD : D.IsRelativeSNC d π) (M : Divisor V) (N : ℕ) (u : Γ(V, cU' D M))
  {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F : ℕ → V.Modules}
  (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
  (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))

/-- The twist `C^•(-A)` is reached: a model of it maps to `K` by a relatively locally exact
inclusion which is a monomorphism in every degree. -/
def Reach (A : Divisor V) : Prop :=
  ∃ (M' : Divisor V) (_ : M' = M + A) (hM : cU' D M' = cU' D M)
    (K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
    (F' : ℕ → V.Modules)
    (e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p))
    (ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M' W))),
    IsCModel d π D hD 0 M' N (V.presheaf.map (homOfLE hM.le).op u) K' F' e' ι' ∧
    ∃ φ : K' ⟶ K, IsTwistInclusion π D M M' hM e e' ι ι' φ ∧ (∀ p, Mono (φ.f p)) ∧
      RelLocallyExact φ

variable {d π D hD M N u e ι} in
/-- If `K` is a model of `C^•`, then the trivial twist `C^•(-0)` is reached, through the identity
of `K`. -/
theorem reach_zero (hK : IsCModel d π D hD 0 M N u K F e ι) : Reach d π D hD M N u e ι 0 := by
  refine ⟨M, (add_zero M).symm, rfl, K, F, e, ι, ?_, 𝟙 K, isTwistInclusion_id π D M e ι,
    fun p => inferInstance, relLocallyExact_id K⟩
  rw [TwistChartForms.presheaf_map_self]
  exact hK

variable {d π D hD M N u e ι} in
/-- If the twist `C^•(-A)` is reached, with `A ≥ 0` supported where `Bn` is, then so is the twist
`C^•(-(A + E))` for every component `E` of `D`. -/
theorem reach_add_single (Bn : Divisor V)
    (hSB : ∀ E, D E = (0 : Divisor V) E + if Bn E = 0 then 0 else 1) (hN : 0 < N)
    (hBn : ∀ E, 0 ≤ Bn E) (ψ : (RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    (hNu : IsUnit ((N : Γ(V, cU' D M)) * u))
    {A : Divisor V} (hA0 : ∀ E, 0 ≤ A E) (hAD : ∀ E, Bn E = 0 → A E = 0)
    (hR : Reach d π D hD M N u e ι A) (E : MMP.Mori.PrimeDivisor V) (hE : E ∈ D.support) :
    Reach d π D hD M N u e ι (A + Finsupp.single E 1) := by
  classical
  obtain ⟨M', hMA, hM, K', F', e', ι', hK', φ, hφ, hmono, hrel⟩ := hR
  have hSBA : ∀ (B : Divisor V), (∀ E, 0 ≤ B E) → (∀ E, Bn E = 0 → B E = 0) →
      ∀ E, D E = (0 : Divisor V) E + if (Bn + (N : ℤ) • B) E = 0 then 0 else 1 :=
    fun B hB0 hBD E => by simp only [hSB E, add_natCast_smul_apply_eq_zero_iff N hBn hB0 hBD E]
  have hBnA : ∀ (B : Divisor V), (∀ E, 0 ≤ B E) → ∀ E, 0 ≤ (Bn + (N : ℤ) • B) E :=
    fun B hB0 => add_natCast_smul_apply_nonneg N hBn hB0
  have hψA : ∀ (B : Divisor V), (N : ℤ) • (M + B) = (Bn + (N : ℤ) • B) + principalDivisor ψ :=
    fun B => by rw [smul_add, hψ]; abel
  set u' := V.presheaf.map (homOfLE hM.le).op u with hu'def
  have hu' : (toRationalFunctionsPresheaf V).app (op (cU' D M')) u' = ratRes (cU' D M') ψ :=
    toRationalFunctionsPresheaf_restrict hM.le u ψ hu
  have hNu' : IsUnit ((N : Γ(V, cU' D M')) * u') := by
    have := hNu.map (V.presheaf.map (homOfLE hM.le).op).hom
    rwa [map_mul, map_natCast] at this
  have hψ' : (N : ℤ) • M' = (Bn + (N : ℤ) • A) + principalDivisor ψ := by rw [hMA]; exact hψA A
  have hBnE : Bn E ≠ 0 := fun h0 => Finsupp.mem_support_iff.1 hE (by simpa [h0] using hSB E)
  have hE' : (Bn + (N : ℤ) • A) E ≠ 0 :=
    (add_natCast_smul_apply_eq_zero_iff N hBn hA0 hAD E).not.2 hBnE
  have hM'' : cU' D (M' + Finsupp.single E 1) = cU' D M' :=
    cU'_add_of_supp_le D M' _ (supp_single_le_supp hE)
  have hA0' : ∀ E', 0 ≤ (A + Finsupp.single E (1 : ℤ) : Divisor V) E' := fun E' => by
    have := hA0 E'
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hAD' : ∀ E', Bn E' = 0 → (A + Finsupp.single E (1 : ℤ) : Divisor V) E' = 0 := by
    intro E' h0
    have hne : E ≠ E' := by rintro rfl; exact hBnE h0
    simp only [Finsupp.add_apply, hAD E' h0, Finsupp.single_apply, if_neg hne, add_zero]
  have hψ'' : (N : ℤ) • (M' + Finsupp.single E 1) =
      (Bn + (N : ℤ) • (A + Finsupp.single E 1)) + principalDivisor ψ := by
    rw [hMA, add_assoc]; exact hψA _
  obtain ⟨K'', F'', e'', ι'', hK''⟩ := exists_isCModel_of_nonneg d π D hD 0
    (M' + Finsupp.single E 1) le_rfl (Bn + (N : ℤ) • (A + Finsupp.single E 1))
    (hSBA _ hA0' hAD') N hN (hBnA _ hA0') ψ hψ'' (V.presheaf.map (homOfLE hM''.le).op u')
    (toRationalFunctionsPresheaf_restrict hM''.le u' ψ hu')
  obtain ⟨φ', hφ', hmono'⟩ := exists_isTwistInclusion π d D hD 0 M' (M' + Finsupp.single E 1) hM''
    N u' (by
      intro E'
      simp only [Finsupp.neg_apply, Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> omega) hNu' hK' hK''
  have hrel' := relLocallyExact_of_isTwistInclusion d π D hD M' (Bn + (N : ℤ) • A)
    (hSBA A hA0 hAD) N hN (hBnA A hA0) ψ hψ' u' hu' e' ι' hK' E hE' hM'' e'' ι'' hK'' φ' hφ'
  haveI := hmono; haveI := hmono'
  refine ⟨M' + Finsupp.single E 1, by rw [hMA, add_assoc], hM''.trans hM, K'', F'', e'', ι'', ?_,
    φ' ≫ φ, hφ.comp hφ', fun p => ?_,
    relLocallyExact_comp_of_mono φ' φ hrel' hrel⟩
  · rwa [hu'def, presheaf_map_map _ _ (homOfLE (hM''.trans hM).le).op] at hK''
  · rw [HomologicalComplex.comp_f]
    infer_instance

variable {d π D hD M N u e ι} in
/-- If `K` is a model of `C^•` and `D` is reduced with support that of `Bn`, then the twist
`C^•(-kD)` is reached for every `k`. -/
theorem reach_nsmul (Bn : Divisor V)
    (hSB : ∀ E, D E = (0 : Divisor V) E + if Bn E = 0 then 0 else 1) (hN : 0 < N)
    (hBn : ∀ E, 0 ≤ Bn E) (ψ : (RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    (hNu : IsUnit ((N : Γ(V, cU' D M)) * u)) (hK : IsCModel d π D hD 0 M N u K F e ι) (k : ℕ) :
    Reach d π D hD M N u e ι (k • D) := by
  classical
  have hD01 : ∀ E, D E = if Bn E = 0 then 0 else 1 := fun E => by
    simpa using hSB E
  have hD0 : ∀ E, 0 ≤ D E := fun E => by rw [hD01 E]; split_ifs <;> omega
  have hDsum : D = ∑ E ∈ D.support, Finsupp.single E (1 : ℤ) := by
    refine Finsupp.ext fun E => ?_
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · have h' := Finsupp.mem_support_iff.1 h
      rw [hD01 E] at h' ⊢
      split_ifs at h' ⊢ <;> simp_all
    · exact Finsupp.notMem_support_iff.1 h
  induction k with
  | zero =>
    rw [zero_smul]
    exact reach_zero hK
  | succ k ih =>
    have key : ∀ T : Finset (MMP.Mori.PrimeDivisor V), T ⊆ D.support →
        Reach d π D hD M N u e ι (k • D + ∑ E ∈ T, Finsupp.single E (1 : ℤ)) := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _; simpa using ih
      | insert E T hET ihT =>
        intro hT
        rw [Finset.sum_insert hET, add_left_comm, add_comm (Finsupp.single E 1)]
        refine reach_add_single Bn hSB hN hBn ψ hψ hu hNu (fun E' => ?_)
          (fun E' h0 => ?_) (ihT ((Finset.subset_insert E T).trans hT)) E
          (hT (Finset.mem_insert_self E T))
        · rw [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, nsmul_eq_mul]
          have := hD0 E'
          have : 0 ≤ ∑ i ∈ T, (Finsupp.single i (1 : ℤ)) E' :=
            Finset.sum_nonneg fun i _ => by
              rw [Finsupp.single_apply]; split_ifs <;> omega
          positivity
        · have hDE : D E' = 0 := by rw [hD01 E', if_pos h0]
          have hnot : E' ∉ T := fun h => (Finsupp.mem_support_iff.1
            (hT (Finset.mem_insert_of_mem h))) hDE
          rw [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, hDE, smul_zero,
            zero_add]
          exact Finset.sum_eq_zero fun i hi => Finsupp.single_eq_of_ne
            (fun h => hnot (h ▸ hi))
    have := key D.support subset_rfl
    rwa [← hDsum, ← succ_nsmul] at this

end Iteration

end MMP.LcBpf
