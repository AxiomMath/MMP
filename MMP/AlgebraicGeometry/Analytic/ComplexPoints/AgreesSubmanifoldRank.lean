module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AlgebraicChartDifferential

/-!
# The rank of the differentials of local equations of a regular subscheme

Let `X` be a scheme over `𝕜 = ℝ` or `ℂ`, `p ∈ X(𝕜)` a point at which `𝒪 = 𝒪_{X,p}` is a regular
local ring of dimension `n`, and `e` an algebraic chart around `p` with values in a space `E` of
dimension `n`. Let `s₁, …, s_r` be regular functions on an affine open `V ∋ p` vanishing at `p`,
whose germs generate an ideal `I` with `𝒪/I` regular of dimension `n - d`. Then the differentials
`d_p sₐ` in the chart span a subspace of the dual of `E` of dimension at least `d`.

Choose `sₐ`, `a ∈ A`, whose differentials form a basis of the span of all the `d_p sₐ`. Every
other `s_b` differs from a combination `∑ cₐ sₐ` with constant coefficients by a function vanishing
at `p` with zero differential, whose germ therefore lies in `𝔪²`
(`MMP.UnderlyingSpace.germ_mem_maximalIdeal_sq_of_chartDeriv_eq_zero`). So
`I ⊆ (sₐ : a ∈ A) + 𝔪²`. Lifting `n - d` generators `x₁, …` of the maximal ideal of `𝒪/I` gives
`𝔪 = (x) + I ⊆ (x) + (sₐ : a ∈ A) + 𝔪²`, hence `𝔪 = (x, sₐ : a ∈ A)` by Nakayama's lemma, and
`n = dim 𝒪 ≤ (n - d) + #A` by Krull's height theorem.

## Main results

* `MMP.UnderlyingSpace.le_finrank_span_chartDeriv`: the differentials of local
  equations of a regular subscheme of codimension `d` at a regular point span a space of
  dimension at least `d`.
* `MMP.UnderlyingSpace.finrank_iInf_ker_chartDeriv_add_le`: equivalently, their
  common kernel has dimension at most `n - d`.
* `MMP.finrank_iInf_ker_add_finrank_span`: the common kernel and the span of
  finitely many linear forms have complementary dimensions.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology IsLocalRing

universe u

namespace MMP

/-- For continuous linear forms `φₐ` on a finite-dimensional space `E`, the common kernel and the
span of the `φₐ` have complementary dimensions. -/
theorem finrank_iInf_ker_add_finrank_span {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {ι : Type*} (φ : ι → E →L[𝕜] 𝕜) :
    Module.finrank 𝕜 (⨅ a, LinearMap.ker (φ a : E →ₗ[𝕜] 𝕜) : Submodule 𝕜 E) +
      Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range φ)) = Module.finrank 𝕜 E := by
  set L := (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] (E →L[𝕜] 𝕜)).symm
  have hW : (Submodule.span 𝕜 (Set.range φ)).map (L : (E →L[𝕜] 𝕜) →ₗ[𝕜] Module.Dual 𝕜 E) =
      Submodule.span 𝕜 (Set.range fun a ↦ (φ a : E →ₗ[𝕜] 𝕜)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hK : (⨅ a, LinearMap.ker (φ a : E →ₗ[𝕜] 𝕜) : Submodule 𝕜 E) =
      (Submodule.span 𝕜 (Set.range fun a ↦ (φ a : E →ₗ[𝕜] 𝕜))).dualCoannihilator := by
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_dualCoannihilator]
    refine ⟨fun h ψ hψ ↦ ?_, fun h a ↦ h _ (Submodule.subset_span ⟨a, rfl⟩)⟩
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ hx hy ↦ by simp [hx, hy])
      (fun _ _ _ hx ↦ by simp [hx]) hψ
    rintro _ ⟨a, rfl⟩
    exact h a
  rw [hK, ← LinearEquiv.finrank_map_eq L, hW, add_comm]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq _

/-- **Nakayama's lemma for a regular quotient.** If `x₁, …, x_q ∈ J` lift generators of the maximal
ideal of a local quotient `O ⧸ I` and `I ≤ J ⊔ 𝔪²`, then `𝔪 ≤ J`. -/
theorem maximalIdeal_le_of_le_sup_sq {O : Type*} [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] {I J : Ideal O} [IsLocalRing (O ⧸ I)] {q : ℕ} (x : Fin q → O)
    (hx : Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk I (x i)) = maximalIdeal (O ⧸ I))
    (hxJ : ∀ i, x i ∈ J) (hIle : I ≤ J ⊔ maximalIdeal O ^ 2) : maximalIdeal O ≤ J := by
  have hIm : I ≤ maximalIdeal O := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O)
    (IsNoetherian.noetherian _) (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ?_
  intro y hy
  have h1 : Ideal.Quotient.mk I y ∈ maximalIdeal (O ⧸ I) := by
    refine (mem_maximalIdeal _).2 fun hu ↦ ?_
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hz
    have : (1 : O) ∈ maximalIdeal O := by
      simpa using (maximalIdeal O).sub_mem (Ideal.mul_mem_right z _ hy) (hIm hz)
    exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  rw [← hx] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
  choose c' hc' using fun i ↦ Ideal.Quotient.mk_surjective (I := I) (c i)
  have hyI : y - ∑ i, c' i * x i ∈ I := by
    rw [← Ideal.Quotient.eq, map_sum, ← hc]
    simp only [map_mul, hc']
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIle hyI)
  rw [smul_eq_mul, ← pow_two, show y = ∑ i, c' i * x i + (y - ∑ i, c' i * x i) by ring, ← hab,
    ← add_assoc]
  exact Submodule.add_mem_sup
    (J.add_mem (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hxJ i)) ha) hb

/-- **Krull's height theorem, counted.** If the maximal ideal of a Noetherian local ring of
dimension `k` is generated by the values of `x : Fin q → O` and `y : κ → O`, then `k ≤ q + #κ`. -/
theorem le_add_of_span_union_eq_maximalIdeal {O : Type*} [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] {k q : ℕ} (hdim : ringKrullDim O = k) (x : Fin q → O) {κ : Type*}
    [Fintype κ] (y : κ → O) (hJ : Ideal.span (Set.range x ∪ Set.range y) = maximalIdeal O) :
    k ≤ q + Fintype.card κ := by
  have h1 := ringKrullDim_le_spanFinrank_maximalIdeal O
  rw [hdim, ← hJ] at h1
  have h2 := Submodule.spanFinrank_span_le_ncard_of_finite (R := O)
    ((Set.finite_range x).union (Set.finite_range y))
  have h3 := Set.ncard_union_le (Set.range x) (Set.range y)
  have h4 : (Set.range x).ncard ≤ q := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
  have h5 : (Set.range y).ncard ≤ Fintype.card κ := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
  have h6 : ((Ideal.span (Set.range x ∪ Set.range y)).spanFinrank : WithBot ℕ∞) ≤
      (q + Fintype.card κ : ℕ) := by
    exact_mod_cast h2.trans (h3.trans (Nat.add_le_add h4 h5))
  exact_mod_cast h1.trans h6

namespace UnderlyingSpace

variable {𝕜 : Type u} [RCLike 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) E} {V : X.Opens} {p : UnderlyingSpace 𝕜 X}

/-- If the differentials at `p` of the subfamily `s ∘ ι` span those of all the `sₐ`, then the germs
of the `sₐ` lie in the ideal generated by the germs of the `s ∘ ι` plus `𝔪²`. -/
theorem span_germ_le_span_germ_sup_maximalIdeal_sq [FiniteDimensional 𝕜 E] {n r : ℕ}
    (hn : Module.finrank 𝕜 E = n) (he : IsAlgebraicChart e) (hp : p ∈ e.source)
    (hV : IsAffineOpen V) (hpV : ⊤ ≤ p.toHom ⁻¹ᵁ V)
    (f : Fin n → X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜)))
    (hf : Ideal.span (Set.range f) = maximalIdeal _) (s : Fin r → Γ(X, V))
    (hs : ∀ a, evalExt V (s a) p = 0) {κ : Type*} [Fintype κ] (ι : κ → Fin r)
    (hspan : Submodule.span 𝕜 (Set.range ((fun a ↦ chartDeriv e V p (s a)) ∘ ι)) =
      Submodule.span 𝕜 (Set.range fun a ↦ chartDeriv e V p (s a))) :
    Ideal.span (Set.range fun a ↦ X.presheaf.germ V _ ((top_le_preimage_iff p V).1 hpV) (s a)) ≤
      Ideal.span (Set.range fun j ↦ X.presheaf.germ V _ ((top_le_preimage_iff p V).1 hpV)
        (s (ι j))) ⊔ maximalIdeal _ ^ 2 := by
  have hxV := (top_le_preimage_iff p V).1 hpV
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a ↦ ?_)
  have hmem : chartDeriv e V p (s a) ∈
      Submodule.span 𝕜 (Set.range ((fun a ↦ chartDeriv e V p (s a)) ∘ ι)) := by
    rw [hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun 𝕜 |>.1 hmem
  set u : Γ(X, V) := s a - ∑ j, constSection V (c j) * s (ι j)
  have hu0 : evalExt V u p = 0 := by
    simp only [u, evalExt_sub hpV, evalExt_sum hpV, evalExt_mul hpV, hs, mul_zero,
      Finset.sum_const_zero, sub_zero]
  have hdu : chartDeriv e V p u = 0 := by
    simp only [u, chartDeriv_sub he hp hpV, chartDeriv_sum he hp hpV, chartDeriv_mul he hp hpV,
      hs, evalExt_constSection hpV, chartDeriv_constSection hp hpV, zero_smul, smul_zero,
      add_zero]
    rw [← hc]
    simp
  have hu := germ_mem_maximalIdeal_sq_of_chartDeriv_eq_zero hn he hp hV hpV f hf u hu0 hdu
  have hsa : X.presheaf.germ V _ hxV (s a) = X.presheaf.germ V _ hxV u +
      ∑ j, X.presheaf.germ V _ hxV (constSection V (c j)) *
        X.presheaf.germ V _ hxV (s (ι j)) := by
    simp only [u, map_sub, map_sum, map_mul, sub_add_cancel]
  rw [SetLike.mem_coe, hsa, add_comm]
  refine Submodule.add_mem_sup (Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ ?_) hu
  exact Ideal.subset_span ⟨j, rfl⟩

/-- **Local equations of a regular subscheme have differentials of rank at least the
codimension.** Let `p ∈ X(𝕜)` be a point at which `𝒪_{X,p}` is regular of dimension `n`, `e` an
algebraic chart around `p` with values in a space of dimension `n`, and `s₁, …, s_r` sections over
an affine open `V ∋ p` vanishing at `p` whose germs generate an ideal `I` with `𝒪_{X,p}/I` regular
of dimension `n - d`. Then the differentials of the `sₐ` at `p` span a space of dimension at
least `d`. -/
theorem le_finrank_span_chartDeriv [FiniteDimensional 𝕜 E] {n d r : ℕ}
    (hn : Module.finrank 𝕜 E = n) (he : IsAlgebraicChart e) (hp : p ∈ e.source)
    (hV : IsAffineOpen V) (hpV : ⊤ ≤ p.toHom ⁻¹ᵁ V)
    [IsRegularLocalRing (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜)))]
    (hdim : ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜))) = n)
    (s : Fin r → Γ(X, V)) (hs : ∀ a, evalExt V (s a) p = 0)
    (hreg : IsRegularLocalRing (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜)) ⧸
      Ideal.span (Set.range fun a ↦ X.presheaf.germ V _ ((top_le_preimage_iff p V).1 hpV) (s a))))
    (hdimq : ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜)) ⧸
      Ideal.span (Set.range fun a ↦ X.presheaf.germ V _ ((top_le_preimage_iff p V).1 hpV) (s a)))
        + d = n) :
    d ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun a ↦ chartDeriv e V p (s a))) := by
  classical
  have hxV := (top_le_preimage_iff p V).1 hpV
  set O := X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜))
  set I : Ideal O := Ideal.span (Set.range fun a ↦ X.presheaf.germ V _ hxV (s a))
  have : IsNoetherianRing O := IsRegularLocalRing.toIsNoetherian
  obtain ⟨k, f, hk, hf⟩ := (isRegularLocalRing_iff_exists_span_eq_maximalIdeal O).1 inferInstance
  obtain rfl : k = n := by exact_mod_cast hk.trans hdim
  have : IsLocalRing (O ⧸ I) := hreg.toIsLocalRing
  obtain ⟨q, fq, hq, hfq⟩ := (isRegularLocalRing_iff_exists_span_eq_maximalIdeal (O ⧸ I)).1 hreg
  have hqd : q + d = k := by
    rw [← hq] at hdimq
    exact_mod_cast hdimq
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (I := I) (fq i)
  obtain rfl : fq = fun i ↦ Ideal.Quotient.mk I (x i) := funext fun i ↦ (hx i).symm
  obtain ⟨κ, ι, hι, hspan, hli⟩ := exists_linearIndependent' 𝕜 (fun a ↦ chartDeriv e V p (s a))
  have : Finite κ := Finite.of_injective ι hι
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun a ↦ chartDeriv e V p (s a))) =
      Fintype.card κ := by
    rw [← hspan]
    exact finrank_span_eq_card hli
  set J : Ideal O := Ideal.span (Set.range x ∪ Set.range fun j ↦ X.presheaf.germ V _ hxV (s (ι j)))
  have hIle : I ≤ J ⊔ maximalIdeal O ^ 2 :=
    (span_germ_le_span_germ_sup_maximalIdeal_sq hn he hp hV hpV f hf s hs ι hspan).trans
      (sup_le_sup_right (Ideal.span_mono Set.subset_union_right) _)
  have hIm : I ≤ maximalIdeal O := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hJ : J = maximalIdeal O := by
    refine le_antisymm (Ideal.span_le.2 ?_) (maximalIdeal_le_of_le_sup_sq x hfq
      (fun i ↦ Ideal.subset_span (Or.inl ⟨i, rfl⟩)) hIle)
    rintro y (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · have : Ideal.Quotient.mk I (x i) ∈ maximalIdeal (O ⧸ I) := by
        rw [← hfq]
        exact Ideal.subset_span ⟨i, rfl⟩
      by_contra hxi
      exact (mem_maximalIdeal _).1 this
        ((IsLocalRing.notMem_maximalIdeal.1 hxi).map (Ideal.Quotient.mk I))
    · exact hIm (Ideal.subset_span ⟨ι j, rfl⟩)
  have := le_add_of_span_union_eq_maximalIdeal hdim x
    (fun j ↦ X.presheaf.germ V _ hxV (s (ι j))) hJ
  rw [hcard]
  omega

/-- **The common kernel of the differentials of local equations of a regular subscheme.** In the
situation of `le_finrank_span_chartDeriv`, the common kernel of the differentials of the `sₐ` at
`p` has dimension at most `n - d`. -/
theorem finrank_iInf_ker_chartDeriv_add_le [FiniteDimensional 𝕜 E] {n d r : ℕ}
    (hn : Module.finrank 𝕜 E = n) (he : IsAlgebraicChart e) (hp : p ∈ e.source)
    (hV : IsAffineOpen V) (hpV : ⊤ ≤ p.toHom ⁻¹ᵁ V)
    [IsRegularLocalRing (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜)))]
    (hdim : ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜))) = n)
    (s : Fin r → Γ(X, V)) (hs : ∀ a, evalExt V (s a) p = 0)
    (hreg : IsRegularLocalRing (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜)) ⧸
      Ideal.span (Set.range fun a ↦ X.presheaf.germ V _ ((top_le_preimage_iff p V).1 hpV) (s a))))
    (hdimq : ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜)) ⧸
      Ideal.span (Set.range fun a ↦ X.presheaf.germ V _ ((top_le_preimage_iff p V).1 hpV) (s a)))
        + d = n) :
    Module.finrank 𝕜
        (⨅ a, LinearMap.ker (chartDeriv e V p (s a) : E →ₗ[𝕜] 𝕜) : Submodule 𝕜 E) + d ≤ n := by
  have h1 := le_finrank_span_chartDeriv hn he hp hV hpV hdim s hs hreg hdimq
  have h2 := finrank_iInf_ker_add_finrank_span fun a ↦ chartDeriv e V p (s a)
  omega

end UnderlyingSpace

end MMP
