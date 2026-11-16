module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksLineSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.AmpleCriterion
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-!
# The zero scheme of the section of the vector bundle given by a global section

For a global section `s` of an `𝒪_X`-module `ℒ`, the zero scheme of the section
`σ_s : X ⟶ 𝐕(ℒ^∨)` (`MMP.Modules.globalSectionMap`) is cut out on every affine open `U` by the
values `λ(s|_U)` of the local functionals `λ ∈ Γ(ℒ^∨, U)`
(`MMP.Modules.ideal_zeroLocus_globalSectionMap`). For `ℒ` invertible it is Stacks' zero scheme
`Z(s)` of Tag 02OQ (`MMP.Modules.zeroLocus_globalSectionMap`).

## References

* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Opposite

namespace MMP.Modules

variable {X : Scheme.{0}} (L : X.Modules) [(Scheme.Modules.dual L).IsQuasicoherent]

/-- The pull-back along `σ_s` of the function `λ` on `π⁻¹U` is `λ(s|_U)`. -/
theorem appLE_globalSectionMap_totalSections (s : Γ(L, ⊤)) (U : X.affineOpens)
    (lam : Γ(Scheme.Modules.dual L, U.1)) :
    (globalSectionMap L s).appLE (proj (Scheme.Modules.dual L) ⁻¹ᵁ U.1) U.1
        (preimage_proj_preimage_globalSectionMap L s U.1).ge
        (totalSections (Scheme.Modules.dual L) U (generator (Scheme.Modules.dual L) U.2 lam)) =
      Scheme.Modules.evalGlobal L s lam := by
  have h := appLE_totalSections_generator (Scheme.Modules.dual L) (globalSectionOver L s) U
    lam (preimage_proj_preimage_globalSectionMap L s U.1).ge
  refine h.trans ((congrArg (fun φ : Scheme.Modules.dual L ⟶
      Scheme.Modules.structurePushforward (𝟙 X) ↦ (φ.val.app (op U.1)).hom lam)
    ((Scheme.Modules.vectorBundleHomEquiv (Scheme.Modules.dual L) (Over.mk (𝟙 X))).apply_symm_apply
      (globalSectionModuleHom L s))).trans rfl)

/-- **The zero scheme of `σ_s` is cut out by the values of the local functionals at `s`.** -/
theorem ideal_zeroLocus_globalSectionMap (s : Γ(L, ⊤)) (U : X.affineOpens) :
    (zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s)).ideal U =
      Ideal.span (range fun lam : Γ(Scheme.Modules.dual L, U.1) ↦
        Scheme.Modules.evalGlobal L s lam) := by
  rw [zeroLocus, Stacks.IdealSheaf.ideal_comap_appLE _ (globalSectionMap L s)
    ⟨proj (Scheme.Modules.dual L) ⁻¹ᵁ U.1, isAffineOpen_proj_preimage _ U⟩ U
    (preimage_proj_preimage_globalSectionMap L s U.1).ge,
    ideal_ker_zeroSection_eq_span_generator, Ideal.map_span, ← range_comp]
  exact congrArg Ideal.span (congrArg Set.range
    (funext fun lam ↦ appLE_globalSectionMap_totalSections L s U lam))

omit [(Scheme.Modules.dual L).IsQuasicoherent] in
/-- The zero scheme of the zero section is all of `X`. -/
lemma zeroLocus_zeroSection (E : X.Modules) [E.IsQuasicoherent] :
    zeroLocus E (zeroSection E) = ⊥ :=
  le_bot_iff.1 (Scheme.IdealSheafData.le_map_iff_comap_le.1
    (Scheme.IdealSheafData.map_bot (zeroSection E)).ge)

/-- A local functional `λ ∈ Γ(ℒ^∨, U)`, as a `Γ(X, U)`-linear form on `Γ(ℒ, U)`. -/
def pairingLinear {U : X.Opens} (lam : Γ(Scheme.Modules.dual L, U)) :
    Γ(L, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun := Scheme.Modules.pairing L lam
  map_add' x y := map_add (lam.app (op (Over.mk (𝟙 U)))).hom x y
  map_smul' a x := Scheme.Modules.pairing_smul_right L lam a x

section Invertible

variable (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]

/-- The dual of an invertible module is finite locally free of rank one. -/
instance isFiniteLocallyFreeOfRank_dual :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0}
      (Scheme.Modules.dual M) 1 :=
  Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
    (X := X) (L := Scheme.Modules.dual M)

end Invertible

variable [Stacks.Ample.IsInvertibleModule X L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The zero scheme of `σ_s : X ⟶ 𝐕(ℒ^∨)` is Stacks' zero scheme `Z(s)`** (Tag 02OQ), for `ℒ`
invertible. -/
theorem zeroLocus_globalSectionMap (s : Γ(L, ⊤)) :
    zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s) =
      Stacks.Divisors.zeroScheme X L s := by
  apply le_antisymm
  · refine Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U ↦ ?_
    rw [ideal_zeroLocus_globalSectionMap, Ideal.span_le]
    rintro _ ⟨lam, rfl⟩
    exact Ideal.subset_span ⟨pairingLinear L lam, rfl⟩
  · have hI := Stacks.ProjectionFormula.isInvertible_of_isInvertibleModule X L
    obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
      (X := X.toRingedSpace) X.ringCatSheaf.2 L
    have hx : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ z, W.1 ≤ V z := fun x ↦ by
      obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := TopologicalSpace.Opens.mem_iSup.mp (hV ▸ trivial)
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hle⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hz (V z).2
      exact ⟨⟨W, hW⟩, hxW, z, hle⟩
    choose W hxW z hWz using hx
    refine Scheme.IdealSheafData.le_of_iSup_eq_top W
      (top_unique fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) fun x ↦ ?_
    obtain ⟨t⟩ := htriv (z x)
    let t' := t.comp (homOfLE (hWz x))
    rw [Stacks.Divisors.zeroScheme_ideal, ideal_zeroLocus_globalSectionMap, Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    rw [Stacks.NonvanishingOpen.eq_triv_smul_basis t'
        (L.presheaf.map (homOfLE (le_top : (W x).1 ≤ ⊤)).op s), map_smul, smul_eq_mul]
    refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Scheme.Modules.trivializationDual t', ?_⟩)
    exact Scheme.Modules.evalGlobal_trivializationDual L t' s

/-- **`σ_s` vanishes only for `s = 0`**, for `ℒ` invertible. -/
theorem eq_zero_of_globalSectionMap_eq_zeroSection (s : Γ(L, ⊤))
    (h : globalSectionMap L s = zeroSection (Scheme.Modules.dual L)) : s = 0 := by
  have hz : zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s) = ⊥ := by
    rw [h, zeroLocus_zeroSection]
  have hI := Stacks.ProjectionFormula.isInvertible_of_isInvertibleModule X L
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  have hx : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ z, W.1 ≤ V z := fun x ↦ by
    obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := TopologicalSpace.Opens.mem_iSup.mp (hV ▸ trivial)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hz (V z).2
    exact ⟨⟨W, hW⟩, hxW, z, hle⟩
  choose W hxW z hWz using hx
  refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨L.presheaf, Scheme.Modules.isSheaf L⟩)
    (U := fun x ↦ (W x).1) ⊤ (fun x ↦ homOfLE le_top)
    (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) s 0 fun x ↦ ?_
  obtain ⟨t⟩ := htriv (z x)
  let t' := t.comp (homOfLE (hWz x))
  have h0 : Scheme.Modules.evalGlobal L s (Scheme.Modules.trivializationDual t') = 0 := by
    have hmem : Scheme.Modules.evalGlobal L s (Scheme.Modules.trivializationDual t') ∈
        (zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s)).ideal (W x) := by
      rw [ideal_zeroLocus_globalSectionMap]
      exact Ideal.subset_span ⟨_, rfl⟩
    rw [hz] at hmem
    simpa using hmem
  rw [Scheme.Modules.evalGlobal_trivializationDual L t' s] at h0
  change L.presheaf.map _ s = L.presheaf.map _ 0
  rw [map_zero, Stacks.NonvanishingOpen.eq_triv_smul_basis t'
    (L.presheaf.map (homOfLE (le_top : (W x).1 ≤ ⊤)).op s)]
  change Stacks.NonvanishingOpen.trivTop t' s • _ = 0
  rw [h0, zero_smul]

end MMP.Modules
