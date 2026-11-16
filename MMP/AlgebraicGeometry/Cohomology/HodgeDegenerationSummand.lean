module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.FrobeniusTwistHypercohomology
public import StacksFrontier.Algebra.Homology.StupidTruncationSplitTriangles
public import StacksFrontier.Algebra.Homology.StupidTruncationSupplement

/-!
# Hodge-to-de Rham degeneration passes to direct summands

Let `π : Y ⟶ T` be a morphism of schemes with `Γ(T, ⊤)` a field `k`, and let `L` be a complex of
sheaves of `π⁻¹𝒪_T`-modules on `Y`, indexed by `ℕ`. Its hypercohomology `ℍ^j(Y, L)` is computed
by the spectral sequence of the stupid filtration `σ^{≥p}L`, with
`E_1^{p,q} = H^q(Y, L^p) ⇒ ℍ^{p+q}(Y, L)`. Without any knowledge of its differentials the
spectral sequence gives the inequality

`dim_k ℍ^k(Y, L) ≤ ∑_{p ≤ k} dim_k H^{k-p}(Y, L^p)`,

as soon as the right-hand side is finite; equality is degeneration at `E₁`. We prove the inequality
directly from the distinguished triangles `σ^{≥p+1}L ⟶ σ^{≥p}L ⟶ L^p[-p] ⟶` of the derived
category, by descending induction on `p`.

Since both sides of the inequality are additive in `L`, equality for `L₁ ⊞ L₂` forces equality
for `L₁` and for `L₂`: degeneration at `E₁` passes to direct summands of complexes. This is the
last step of the covering argument for the fractional logarithmic complex, where `C^•` is a
direct summand of the direct image of a logarithmic de Rham complex along a finite cover.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.finite_and_finrank_le_of_exact`: the linear algebra
  of a three-term exact sequence.
* `MMP.FourfoldProofs.FractionalLogComplexProof.finite_and_finrank_hyp_le_of_distinguished`: the
  inequality for a distinguished triangle of the bounded below derived category.
* `MMP.FourfoldProofs.FractionalLogComplexProof.finite_and_finrank_hyp_le_sum`: the `E₁`-inequality
  `dim ℍ^k(Y, K) ≤ ∑_{p ≤ k} dim H^{k-p}(Y, Kᵖ)` for a complex `K` indexed by `ℕ`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.finrank_hyp_eq_sum_of_biprod` and
  `MMP.FourfoldProofs.FractionalLogComplexProof.finrank_hyp_eq_sum_of_retract`: the equality
  (degeneration at `E₁`) passes from `L₁ ⊞ L₂` to `L₁` and `L₂`, and from a complex to its
  retracts.

## Implementation notes

Hypercohomology is the right derived functor of global sections on the bounded below derived
category, read over `Γ(T, ⊤)` (`MMP.Mori.Divisor.LogSpreadingProof.Hc`), as in the statements of
the logarithmic degeneration theorems; `MMP.FourfoldProofs.FractionalLogComplexProof.hyp` is the same
construction on objects of the derived category. The stupid filtration is taken on the extension
of `K` by zero to `ℤ`.

## References

* [P. Deligne, *Théorie de Hodge II*][Deligne1971]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open MMP.Mori.Divisor.LogSpreadingProof MMP.FourfoldProofs.LogDegenerationProof

/-! ### A three-term exact sequence of vector spaces -/

/-- **Dimension in an exact sequence.** If `M₁ ⟶ M₂ ⟶ M₃` is exact over a field and `M₁`, `M₃`
are finite dimensional, then so is `M₂`, and `dim M₂ ≤ dim M₁ + dim M₃`. -/
theorem finite_and_finrank_le_of_exact {K M₁ M₂ M₃ : Type*} [DivisionRing K] [AddCommGroup M₁]
    [Module K M₁] [AddCommGroup M₂] [Module K M₂] [AddCommGroup M₃] [Module K M₃]
    (f : M₁ →ₗ[K] M₂) (g : M₂ →ₗ[K] M₃) (h : Function.Exact f g)
    [Module.Finite K M₁] [Module.Finite K M₃] :
    Module.Finite K M₂ ∧ Module.finrank K M₂ ≤ Module.finrank K M₁ + Module.finrank K M₃ := by
  have hk : LinearMap.ker g = LinearMap.range f := h.linearMap_ker_eq
  have : Module.Finite K (LinearMap.ker g) := by
    rw [hk]
    infer_instance
  have : Module.Finite K (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv (g.quotKerEquivRange).symm
  have : Module.Finite K M₂ := Module.Finite.of_submodule_quotient (LinearMap.ker g)
  refine ⟨inferInstance, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K M₁ :=
    hk ▸ LinearMap.finrank_range_le f
  have h3 := Submodule.finrank_le (LinearMap.range g)
  omega

/-! ### Hypercohomology of objects of the bounded below derived category -/

section Hyp

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

/-- The sheaf of rings `π⁻¹𝒪_T` on `Y`, for `π = h`. -/
noncomputable abbrev invRing : Sheaf (Opens.grothendieckTopology Y) RingCat.{0} :=
  SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)

/-- The map `Γ(T, ⊤) → Γ(Y, π⁻¹𝒪_T)` through which hypercohomology is read over `Γ(T, ⊤)`. -/
noncomputable abbrev invRingUnit : Γ(T, ⊤) →+*
    ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf).obj.obj (op ⊤) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} h.base).unit.app
    T.sheaf).hom.app (op ⊤)).hom

/-- Global sections of sheaves of `π⁻¹𝒪_T`-modules. -/
noncomputable abbrev globalSections :=
  SheafOfModules.evaluation.{0} (invRing h) (op ⊤)

/-- `ℍ^j(Y, X)` over `Γ(T, ⊤)` for an object `X` of the bounded below derived category of
`π⁻¹𝒪_T`-modules: the `j`-th homology of the right derived functor of global sections. -/
noncomputable def hyp (X : DerivedCategory.Plus (SheafOfModules.{0} (invRing h))) (j : ℤ) :
    ModuleCat.{0} Γ(T, ⊤) :=
  (ModuleCat.restrictScalars.{0} (invRingUnit h)).obj
    ((DerivedCategory.homologyFunctor (ModuleCat.{0} ((invRing h).obj.obj (op ⊤))) j).obj
      (DerivedCategory.Plus.ι.obj ((globalSections h).rightDerivedFunctorPlus.obj X)))

/-- On a bounded below complex, `hyp` is the hypercohomology `Hc` of the statements. -/
theorem hyp_Q_obj (K : CochainComplex.Plus (SheafOfModules.{0} (invRing h))) (j : ℤ) :
    hyp h (DerivedCategory.Plus.Q.obj K) j = Hc h K j := rfl

/-- `hyp` is functorial: it is the image of a functor on the derived category. -/
noncomputable def hypFunctor (j : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{0} (invRing h)) ⥤ ModuleCat.{0} Γ(T, ⊤) :=
  (globalSections h).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{0} ((invRing h).obj.obj (op ⊤))) j ⋙
      ModuleCat.restrictScalars.{0} (invRingUnit h)

/-- The functor `hypFunctor h j` sends `X` to `hyp h X j`. -/
@[simp]
theorem hypFunctor_obj (j : ℤ) (X : DerivedCategory.Plus (SheafOfModules.{0} (invRing h))) :
    (hypFunctor h j).obj X = hyp h X j := rfl

/-- **The inequality for a distinguished triangle.** For a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` of the bounded below derived category, if `ℍ^j(X₁)` and `ℍ^j(X₃)` are
finite dimensional over the field `Γ(T, ⊤)`, then so is `ℍ^j(X₂)`, and
`dim ℍ^j(X₂) ≤ dim ℍ^j(X₁) + dim ℍ^j(X₃)`. -/
theorem finite_and_finrank_hyp_le_of_distinguished (hT : IsField Γ(T, ⊤))
    (Tr : Pretriangulated.Triangle (DerivedCategory.Plus (SheafOfModules.{0} (invRing h))))
    (hTr : Tr ∈ distTriang _) (j : ℤ) [Module.Finite Γ(T, ⊤) (hyp h Tr.obj₁ j)]
    [Module.Finite Γ(T, ⊤) (hyp h Tr.obj₃ j)] :
    Module.Finite Γ(T, ⊤) (hyp h Tr.obj₂ j) ∧
      Module.finrank Γ(T, ⊤) (hyp h Tr.obj₂ j) ≤
        Module.finrank Γ(T, ⊤) (hyp h Tr.obj₁ j) + Module.finrank Γ(T, ⊤) (hyp h Tr.obj₃ j) := by
  let := hT.toField
  let := Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus (globalSections h)
  have := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus (globalSections h)
  let G := (globalSections h).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{0} ((invRing h).obj.obj (op ⊤))) j
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (G.map_distinguished_exact Tr hTr)
  have hz : G.map Tr.mor₁ ≫ G.map Tr.mor₂ = 0 := by
    rw [← Functor.map_comp, Pretriangulated.comp_distTriang_mor_zero₁₂ _ hTr, Functor.map_zero]
  let f := ((ModuleCat.restrictScalars.{0} (invRingUnit h)).map (G.map Tr.mor₁)).hom
  let g := ((ModuleCat.restrictScalars.{0} (invRingUnit h)).map (G.map Tr.mor₂)).hom
  have hfg : Function.Exact f g := fun y => by
    refine ⟨fun hy => hex y hy, ?_⟩
    rintro ⟨x, rfl⟩
    exact congrArg (fun φ => φ.hom x) hz
  exact finite_and_finrank_le_of_exact (K := Γ(T, ⊤)) (M₁ := hyp h Tr.obj₁ j)
    (M₂ := hyp h Tr.obj₂ j) (M₃ := hyp h Tr.obj₃ j) f g hfg

end Hyp

/-! ### The triangles of the stupid filtration -/

section Truncation

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

open HomologicalComplex ComplexShape StacksDraft.StupidTruncation

/-- The brutal truncation `σ^{≥p}X` of a cochain complex, as a bounded below complex. -/
noncomputable def truncGE (X : CochainComplex (SheafOfModules.{0} (invRing h)) ℤ) (p : ℤ) :
    CochainComplex.Plus (SheafOfModules.{0} (invRing h)) :=
  ⟨X.stupidTrunc (embeddingUpIntGE p), p, inferInstance⟩

/-- **The triangle `σ^{≥p+1}X ⟶ σ^{≥p}X ⟶ Xᵖ[-p] ⟶` in the bounded below derived category.**
There is a distinguished triangle of `D⁺` whose first two vertices are `σ^{≥p+1}X`, `σ^{≥p}X`
and whose third vertex is isomorphic to `Xᵖ` placed in degree `p`. -/
theorem exists_distinguished_truncGE (X : CochainComplex (SheafOfModules.{0} (invRing h)) ℤ)
    (p : ℤ) :
    ∃ Tr : Pretriangulated.Triangle (DerivedCategory.Plus (SheafOfModules.{0} (invRing h))),
      Tr ∈ distTriang _ ∧ Tr.obj₁ = DerivedCategory.Plus.Q.obj (truncGE h X (p + 1)) ∧
        Tr.obj₂ = DerivedCategory.Plus.Q.obj (truncGE h X p) ∧
        Nonempty (Tr.obj₃ ≅ (DerivedCategory.Plus.singleFunctor _ p).obj (X.X p)) := by
  let f : truncGE h X (p + 1) ⟶ truncGE h X p :=
    ObjectProperty.homMk (stupidTruncGEMapLE X (show p ≤ p + 1 by omega))
  obtain ⟨Z, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    (DerivedCategory.Plus.Q.map f)
  refine ⟨_, hT, rfl, rfl, ?_⟩
  have h₁ := DerivedCategory.Plus.ι.map_distinguished _ hT
  have h₂ := stupidTruncGESplitTriangleQ_distinguished X p
  obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ h₁ h₂ (Iso.refl _)
  exact ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (Pretriangulated.Triangle.π₃.mapIso e ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ p).app (X.X p)).symm)⟩

/-- **`ℍ^k(M[-p]) ≅ H^{k-p}(M)`.** For a sheaf `M`, the hypercohomology in degree `k` of `M`
placed in degree `p` is linearly equivalent to that in degree `k - p` of `M` placed in degree
`0`. -/
theorem nonempty_hyp_singleFunctor_linearEquiv (M : SheafOfModules.{0} (invRing h)) (p k : ℤ) :
    Nonempty (hyp h ((DerivedCategory.Plus.singleFunctor _ p).obj M) k ≃ₗ[Γ(T, ⊤)]
      hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj M) (k - p)) := by
  let := Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus (globalSections h)
  have := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus (globalSections h)
  let F := (globalSections h).rightDerivedFunctorPlus
  let G := F ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ((invRing h).obj.obj (op ⊤))) k
  let E := G.mapIso (((DerivedCategory.Plus.singleFunctors _).shiftIso (-p) p 0
      (by simp)).app M).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ k).mapIso ((F.commShiftIso (-p)).app _) ≪≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso (-p) k (k - p) (by omega)).app _
  exact ⟨((ModuleCat.restrictScalars.{0} (invRingUnit h)).mapIso E).toLinearEquiv⟩

/-- A complex that is strictly concentrated in degrees `≥ n` has no hypercohomology below `n`. -/
theorem subsingleton_hyp_of_isStrictlyGE (K : CochainComplex.Plus (SheafOfModules.{0} (invRing h)))
    (n : ℤ) [K.obj.IsStrictlyGE n] (j : ℤ) (hj : j < n) :
    Subsingleton (hyp h (DerivedCategory.Plus.Q.obj K) j) := by
  have : (DerivedCategory.Plus.Q.obj K).IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj K.obj).IsGE n
    infer_instance
  have := CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj (globalSections h)
    (DerivedCategory.Plus.Q.obj K) n
  have hZ := DerivedCategory.Plus.isZero_homology_of_isGE
    ((globalSections h).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) n j hj
  have hsub := ModuleCat.isZero_iff_subsingleton.1 hZ
  exact hsub

end Truncation

/-! ### The inequality `dim ℍ^k ≤ ∑ dim E₁^{p, k-p}` -/

section Inequality

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

open HomologicalComplex ComplexShape StacksDraft.StupidTruncation

/-- Finite dimensionality and dimension are invariant under an isomorphism of the derived
category. -/
theorem finite_and_finrank_hyp_eq_of_iso
    {X X' : DerivedCategory.Plus (SheafOfModules.{0} (invRing h))}
    (e : X ≅ X') (j : ℤ) :
    (Module.Finite Γ(T, ⊤) (hyp h X j) ↔ Module.Finite Γ(T, ⊤) (hyp h X' j)) ∧
      Module.finrank Γ(T, ⊤) (hyp h X j) = Module.finrank Γ(T, ⊤) (hyp h X' j) :=
  let e' : hyp h X j ≃ₗ[Γ(T, ⊤)] hyp h X' j := ((hypFunctor h j).mapIso e).toLinearEquiv
  ⟨⟨fun _ => Module.Finite.equiv e', fun _ => Module.Finite.equiv e'.symm⟩, e'.finrank_eq⟩

/-- **The inequality along the stupid filtration.** For a cochain complex `X` and integers `k`,
`m`, if `H^q(X^{k-q})` is finite dimensional for `q < m`, then `ℍ^k(σ^{≥k+1-m}X)` is finite
dimensional of dimension at most `∑_{q < m} dim H^q(X^{k-q})`. -/
theorem finite_and_finrank_hyp_truncGE_le (hT : IsField Γ(T, ⊤))
    (X : CochainComplex (SheafOfModules.{0} (invRing h)) ℤ) (k : ℤ) (m : ℕ)
    (hfin : ∀ q : ℕ, q < m →
      Module.Finite Γ(T, ⊤)
        (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj (X.X (k - q))) q)) :
    Module.Finite Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X (k + 1 - m))) k) ∧
      Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X (k + 1 - m))) k) ≤
        ∑ q ∈ Finset.range m, Module.finrank Γ(T, ⊤)
          (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj (X.X (k - q))) q) := by
  induction m with
  | zero =>
    have : (truncGE h X (k + 1 - ((0 : ℕ) : ℤ))).obj.IsStrictlyGE (k + 1 - ((0 : ℕ) : ℤ)) :=
      inferInstanceAs (CochainComplex.IsStrictlyGE (X.stupidTrunc (embeddingUpIntGE _)) _)
    have := subsingleton_hyp_of_isStrictlyGE h (truncGE h X (k + 1 - ((0 : ℕ) : ℤ)))
      (k + 1 - ((0 : ℕ) : ℤ)) k (by omega)
    have : Nontrivial Γ(T, ⊤) := ⟨hT.exists_pair_ne⟩
    exact ⟨inferInstance, Module.finrank_zero_of_subsingleton.trans_le (Nat.zero_le _)⟩
  | succ m ih =>
    obtain ⟨hf₁, hr₁⟩ := ih fun q hq => hfin q (by omega)
    obtain ⟨Tr, hTr, h₁, h₂, ⟨e₃⟩⟩ := exists_distinguished_truncGE h X (k - m)
    have k₁ : k - (m : ℤ) + 1 = k + 1 - m := by omega
    have k₂ : k - (m : ℤ) = k + 1 - ((m + 1 : ℕ) : ℤ) := by push_cast; omega
    rw [k₁] at h₁
    rw [k₂] at h₂
    obtain ⟨e₀⟩ := nonempty_hyp_singleFunctor_linearEquiv h (X.X (k - m)) (k - m) k
    have hk : k - (k - (m : ℤ)) = (m : ℤ) := by omega
    rw [hk] at e₀
    have := hfin m (by omega)
    have : Module.Finite Γ(T, ⊤) (hyp h ((DerivedCategory.Plus.singleFunctor _ (k - m)).obj
      (X.X (k - m))) k) := Module.Finite.equiv e₀.symm
    have i₃ := finite_and_finrank_hyp_eq_of_iso h e₃ k
    have : Module.Finite Γ(T, ⊤) (hyp h Tr.obj₃ k) := i₃.1.2 inferInstance
    have : Module.Finite Γ(T, ⊤) (hyp h Tr.obj₁ k) := h₁ ▸ hf₁
    obtain ⟨hf₂, hr₂⟩ := finite_and_finrank_hyp_le_of_distinguished h hT Tr hTr k
    rw [h₂] at hf₂ hr₂
    rw [h₁] at hr₂
    refine ⟨hf₂, hr₂.trans ?_⟩
    rw [Finset.sum_range_succ, i₃.2, e₀.symm.finrank_eq.symm]
    omega

/-- The sheaf `M` placed in degree `0`, as a complex or through the single functor of the derived
category. -/
noncomputable def qObjSingle0Iso (M : SheafOfModules.{0} (invRing h)) :
    DerivedCategory.Plus.Q.obj (single0 h M) ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj M :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm

/-- The term `Kᵖ` of a complex indexed by `ℕ`, read in its extension to `ℤ` and placed in
degree `0`, is the complex `single0 h (Kᵖ)` of the statements. -/
noncomputable def singleFunctorExtendXIso (K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ)
    (p : ℕ) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((K.extend embeddingUpNat).X (p : ℤ)) ≅
      DerivedCategory.Plus.Q.obj (single0 h (K.X p)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).mapIso (K.extendXIso embeddingUpNat rfl) ≪≫
    (qObjSingle0Iso h (K.X p)).symm

/-- **The `E₁`-inequality.** Let `K` be a complex of sheaves of `π⁻¹𝒪_T`-modules indexed by `ℕ`,
with `Γ(T, ⊤)` a field. If `H^{k-p}(Y, Kᵖ)` is finite dimensional for every `p ≤ k`, then so is
`ℍ^k(Y, K)`, and `dim ℍ^k(Y, K) ≤ ∑_{p ≤ k} dim H^{k-p}(Y, Kᵖ)`. -/
theorem finite_and_finrank_hyp_le_sum (hT : IsField Γ(T, ⊤))
    (K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ) (k : ℕ)
    (hfin : ∀ p ∈ Finset.range (k + 1),
      Module.Finite Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ))) :
    Module.Finite Γ(T, ⊤) (Hc h ⟨K.extend ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) ∧
      Module.finrank Γ(T, ⊤) (Hc h ⟨K.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) ≤
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ)) := by
  let X := K.extend ComplexShape.embeddingUpNat
  -- the terms, reindexed by `q = k - p`
  have hterm : ∀ q ∈ Finset.range (k + 1),
      (Module.Finite Γ(T, ⊤)
          (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj (X.X ((k : ℤ) - (q : ℕ)))) q) ↔
        Module.Finite Γ(T, ⊤) (Hc h (single0 h (K.X (k - q))) ((k - (k - q) : ℕ) : ℤ))) ∧
      Module.finrank Γ(T, ⊤)
          (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj (X.X ((k : ℤ) - (q : ℕ)))) q) =
        Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X (k - q))) ((k - (k - q) : ℕ) : ℤ)) := by
    intro q hq
    rw [Finset.mem_range] at hq
    have e₁ : (k : ℤ) - (q : ℕ) = ((k - q : ℕ) : ℤ) := by omega
    have e₂ : (q : ℤ) = ((k - (k - q) : ℕ) : ℤ) := by omega
    rw [e₁, e₂]
    exact finite_and_finrank_hyp_eq_of_iso h (singleFunctorExtendXIso h K (k - q)) _
  obtain ⟨hf, hr⟩ := finite_and_finrank_hyp_truncGE_le h hT X k (k + 1) fun q hq =>
    (hterm q (Finset.mem_range.2 hq)).1.2
      (hfin (k - q) (Finset.mem_range.2 (by omega)))
  have e₀ : (k : ℤ) + 1 - ((k + 1 : ℕ) : ℤ) = 0 := by push_cast; ring
  rw [e₀] at hf hr
  -- `σ^{≥0}X = X`
  have : X.IsStrictlySupported (embeddingUpIntGE 0) :=
    CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat K
  have hI : IsIso (HomologicalComplex.ιStupidTrunc X (embeddingUpIntGE 0)) :=
    StacksDraft.StupidTruncation.isIso_ιStupidTrunc _ _
  let ι₀ : truncGE h X 0 ≅
      ⟨X, 0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ :=
    (ObjectProperty.fullyFaithfulι _).preimageIso
      (@asIso _ _ _ _ (HomologicalComplex.ιStupidTrunc X (embeddingUpIntGE 0)) hI)
  have i₀ := finite_and_finrank_hyp_eq_of_iso h (DerivedCategory.Plus.Q.mapIso ι₀) (k : ℤ)
  refine ⟨i₀.1.1 hf, ?_⟩
  rw [← hyp_Q_obj, ← i₀.2]
  refine hr.trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun q hq => (hterm q hq).2]
  exact Finset.sum_range_reflect
    (fun p => Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ))) (k + 1)

end Inequality

/-! ### Additivity -/

section Additivity

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

/-- The functor `hypFunctor h j` is additive. -/
instance (j : ℤ) : (hypFunctor h j).Additive := by
  let := Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus (globalSections h)
  have := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus (globalSections h)
  have : (globalSections h).rightDerivedFunctorPlus.Additive := inferInstance
  have : (DerivedCategory.homologyFunctor
      (ModuleCat.{0} ((invRing h).obj.obj (op ⊤))) j).Additive :=
    inferInstance
  have : (ModuleCat.restrictScalars.{0} (invRingUnit h)).Additive := inferInstance
  have : (DerivedCategory.Plus.ι :
      DerivedCategory.Plus (SheafOfModules.{0} (invRing h)) ⥤ _).Additive :=
    inferInstance
  refine ⟨fun {X Y f g} => ?_⟩
  change (ModuleCat.restrictScalars.{0} (invRingUnit h)).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{0} ((invRing h).obj.obj (op ⊤))) j).map
        (DerivedCategory.Plus.ι.map ((globalSections h).rightDerivedFunctorPlus.map (f + g)))) = _
  rw [Functor.map_add, Functor.map_add, Functor.map_add]
  exact (ModuleCat.restrictScalars.{0} (invRingUnit h)).map_add

/-- `ℍ^j(Y, -)` on complexes indexed by `ℕ`, through their extension by zero to `ℤ`. -/
noncomputable def hypComplexFunctor (j : ℤ) :
    CochainComplex (SheafOfModules.{0} (invRing h)) ℕ ⥤ ModuleCat.{0} Γ(T, ⊤) :=
  ObjectProperty.lift _ (ComplexShape.embeddingUpNat.extendFunctor _)
      (fun L => ⟨0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat L⟩) ⋙
    DerivedCategory.Plus.Q ⋙ hypFunctor h j

/-- The functor `hypComplexFunctor h j` sends `L` to the hypercohomology of its extension by zero
to `ℤ`. -/
theorem hypComplexFunctor_obj (j : ℤ) (L : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ) :
    (hypComplexFunctor h j).obj L = Hc h ⟨L.extend ComplexShape.embeddingUpNat, 0,
      CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j := rfl

/-- The functor `hypComplexFunctor h j` is additive. -/
instance (j : ℤ) : (hypComplexFunctor h j).Additive := by
  have : (DerivedCategory.Plus.Q :
      CochainComplex.Plus (SheafOfModules.{0} (invRing h)) ⥤ _).Additive :=
    Functor.instAdditiveFullSubcategoryLift _ _ _
  have : ((CochainComplex.plus (SheafOfModules.{0} (invRing h))).lift
      (ComplexShape.embeddingUpNat.extendFunctor (SheafOfModules.{0} (invRing h)))
      (fun L => ⟨0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat L⟩)).Additive :=
    Functor.instAdditiveFullSubcategoryLift _ _ _
  exact Functor.instAdditiveComp _ _

/-- **Dimensions add over a biproduct.** For an additive functor `G` to modules over a field and a
biproduct `X₁ ⊞ X₂` with `G(X₁ ⊞ X₂)` finite dimensional, the spaces `G X₁`, `G X₂` are finite
dimensional and `dim G(X₁ ⊞ X₂) = dim G X₁ + dim G X₂`. -/
theorem finite_and_finrank_biprod {R : Type} [CommRing R] (hR : IsField R) {C : Type*}
    [Category C] [Preadditive C] [HasBinaryBiproducts C] (G : C ⥤ ModuleCat.{0} R) [G.Additive]
    (X₁ X₂ : C) [Module.Finite R (G.obj (X₁ ⊞ X₂))] :
    Module.Finite R (G.obj X₁) ∧ Module.Finite R (G.obj X₂) ∧
      Module.finrank R (G.obj (X₁ ⊞ X₂)) =
        Module.finrank R (G.obj X₁) + Module.finrank R (G.obj X₂) := by
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  let e : G.obj (X₁ ⊞ X₂) ≃ₗ[R] (G.obj X₁ × G.obj X₂) :=
    (G.mapBiprod X₁ X₂ ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  have : Module.Finite R (G.obj X₁ × G.obj X₂) := Module.Finite.equiv e
  have h₁ : Module.Finite R (G.obj X₁) :=
    Module.Finite.of_surjective (LinearMap.fst R (G.obj X₁) (G.obj X₂)) LinearMap.fst_surjective
  have h₂ : Module.Finite R (G.obj X₂) :=
    Module.Finite.of_surjective (LinearMap.snd R (G.obj X₁) (G.obj X₂)) LinearMap.snd_surjective
  have : Module.Free R (G.obj X₁) := by let := hR.toField; exact Module.Free.of_divisionRing _ _
  have : Module.Free R (G.obj X₂) := by let := hR.toField; exact Module.Free.of_divisionRing _ _
  have : Nontrivial R := ⟨hR.exists_pair_ne⟩
  exact ⟨h₁, h₂, e.finrank_eq.trans (Module.finrank_prod (R := R))⟩

/-- `H^j(Y, M)` as a functor of the sheaf `M`. -/
noncomputable def hypSheafFunctor (j : ℤ) :
    SheafOfModules.{0} (invRing h) ⥤ ModuleCat.{0} Γ(T, ⊤) :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ hypFunctor h j

/-- The functor `hypSheafFunctor h j` sends `M` to the hypercohomology of `M` placed in degree
`0`. -/
@[simp]
theorem hypSheafFunctor_obj (j : ℤ) (M : SheafOfModules.{0} (invRing h)) :
    (hypSheafFunctor h j).obj M = hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj M) j :=
  rfl

/-- The functor `hypSheafFunctor h j` is additive. -/
instance (j : ℤ) : (hypSheafFunctor h j).Additive :=
  inferInstanceAs (DerivedCategory.Plus.singleFunctor _ 0 ⋙ hypFunctor h j).Additive

/-- `Hc h (single0 h M) j` and `(hypSheafFunctor h j).obj M` are finite dimensional together,
and have the same dimension. -/
theorem finite_and_finrank_hypSheafFunctor (M : SheafOfModules.{0} (invRing h)) (j : ℤ) :
    (Module.Finite Γ(T, ⊤) (Hc h (single0 h M) j) ↔
        Module.Finite Γ(T, ⊤) ((hypSheafFunctor h j).obj M)) ∧
      Module.finrank Γ(T, ⊤) (Hc h (single0 h M) j) =
        Module.finrank Γ(T, ⊤) ((hypSheafFunctor h j).obj M) :=
  finite_and_finrank_hyp_eq_of_iso h (qObjSingle0Iso h M) j

end Additivity

/-! ### Degeneration passes to direct summands -/

section Summand

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

/-- **`E₁`-degeneration passes to the summands of a biproduct.** Let `L₁`, `L₂` be complexes of
sheaves of `π⁻¹𝒪_T`-modules indexed by `ℕ`, with `Γ(T, ⊤)` a field. If the Hodge groups
`H^{k-p}(L₁ᵖ ⊞ L₂ᵖ)`, `p ≤ k`, are finite dimensional and
`dim ℍ^k(L₁ ⊞ L₂) = ∑_{p ≤ k} dim H^{k-p}(L₁ᵖ ⊞ L₂ᵖ)`, then the same equality holds for `L₁`
and for `L₂`. -/
theorem finrank_hyp_eq_sum_of_biprod (hT : IsField Γ(T, ⊤))
    (L₁ L₂ : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ) (k : ℕ)
    (hfin : ∀ p ∈ Finset.range (k + 1),
      Module.Finite Γ(T, ⊤) (Hc h (single0 h ((L₁ ⊞ L₂).X p)) ((k - p : ℕ) : ℤ)))
    (heq : Module.finrank Γ(T, ⊤) (Hc h ⟨(L₁ ⊞ L₂).extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(T, ⊤) (Hc h (single0 h ((L₁ ⊞ L₂).X p)) ((k - p : ℕ) : ℤ))) :
    Module.finrank Γ(T, ⊤) (Hc h ⟨L₁.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(T, ⊤) (Hc h (single0 h (L₁.X p)) ((k - p : ℕ) : ℤ)) ∧
      Module.finrank Γ(T, ⊤) (Hc h ⟨L₂.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(T, ⊤) (Hc h (single0 h (L₂.X p)) ((k - p : ℕ) : ℤ)) := by
  -- the Hodge groups, term by term
  have hterm : ∀ p ∈ Finset.range (k + 1),
      Module.Finite Γ(T, ⊤) (Hc h (single0 h (L₁.X p)) ((k - p : ℕ) : ℤ)) ∧
      Module.Finite Γ(T, ⊤) (Hc h (single0 h (L₂.X p)) ((k - p : ℕ) : ℤ)) ∧
      Module.finrank Γ(T, ⊤) (Hc h (single0 h ((L₁ ⊞ L₂).X p)) ((k - p : ℕ) : ℤ)) =
        Module.finrank Γ(T, ⊤) (Hc h (single0 h (L₁.X p)) ((k - p : ℕ) : ℤ)) +
          Module.finrank Γ(T, ⊤) (Hc h (single0 h (L₂.X p)) ((k - p : ℕ) : ℤ)) := by
    intro p hp
    let G := hypSheafFunctor h ((k - p : ℕ) : ℤ)
    let e : G.obj ((L₁ ⊞ L₂).X p) ≃ₗ[Γ(T, ⊤)] G.obj (L₁.X p ⊞ L₂.X p) :=
      (G.mapIso ((HomologicalComplex.eval _ _ p).mapBiprod L₁ L₂)).toLinearEquiv
    have i₀ := finite_and_finrank_hypSheafFunctor h ((L₁ ⊞ L₂).X p) ((k - p : ℕ) : ℤ)
    have i₁ := finite_and_finrank_hypSheafFunctor h (L₁.X p) ((k - p : ℕ) : ℤ)
    have i₂ := finite_and_finrank_hypSheafFunctor h (L₂.X p) ((k - p : ℕ) : ℤ)
    have := i₀.1.1 (hfin p hp)
    have : Module.Finite Γ(T, ⊤) (G.obj (L₁.X p ⊞ L₂.X p)) := Module.Finite.equiv e
    obtain ⟨f₁, f₂, hr⟩ := finite_and_finrank_biprod hT G (L₁.X p) (L₂.X p)
    exact ⟨i₁.1.2 f₁, i₂.1.2 f₂, by rw [i₀.2, i₁.2, i₂.2, e.finrank_eq, hr]⟩
  -- the inequalities
  obtain ⟨hK, -⟩ := finite_and_finrank_hyp_le_sum h hT (L₁ ⊞ L₂) k hfin
  obtain ⟨-, h₁⟩ := finite_and_finrank_hyp_le_sum h hT L₁ k fun p hp => (hterm p hp).1
  obtain ⟨-, h₂⟩ := finite_and_finrank_hyp_le_sum h hT L₂ k fun p hp => (hterm p hp).2.1
  -- additivity of the hypercohomology
  have : Module.Finite Γ(T, ⊤) ((hypComplexFunctor h k).obj (L₁ ⊞ L₂)) := hK
  obtain ⟨-, -, hA⟩ := finite_and_finrank_biprod hT (hypComplexFunctor h k) L₁ L₂
  rw [hypComplexFunctor_obj, hypComplexFunctor_obj, hypComplexFunctor_obj] at hA
  rw [Finset.sum_congr rfl fun p hp => (hterm p hp).2.2, Finset.sum_add_distrib] at heq
  omega

/-- **`E₁`-degeneration passes to retracts.** Let `L` be a retract of `K` in the category of
complexes of sheaves of `π⁻¹𝒪_T`-modules indexed by `ℕ` (`i : L ⟶ K`, `r : K ⟶ L`,
`i ≫ r = 𝟙`), with `Γ(T, ⊤)` a field. If the Hodge groups `H^{k-p}(Kᵖ)`, `p ≤ k`, are finite
dimensional and `dim ℍ^k(K) = ∑_{p ≤ k} dim H^{k-p}(Kᵖ)`, then
`dim ℍ^k(L) = ∑_{p ≤ k} dim H^{k-p}(Lᵖ)`. -/
theorem finrank_hyp_eq_sum_of_retract (hT : IsField Γ(T, ⊤))
    {L K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ} (i : L ⟶ K) (r : K ⟶ L)
    (hir : i ≫ r = 𝟙 L) (k : ℕ)
    (hfin : ∀ p ∈ Finset.range (k + 1),
      Module.Finite Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ)))
    (heq : Module.finrank Γ(T, ⊤) (Hc h ⟨K.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ))) :
    Module.finrank Γ(T, ⊤) (Hc h ⟨L.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1),
          Module.finrank Γ(T, ⊤) (Hc h (single0 h (L.X p)) ((k - p : ℕ) : ℤ)) := by
  have : IsSplitMono i := ⟨⟨⟨r, hir⟩⟩⟩
  let e : K ≅ L ⊞ cokernel i := biprod.uniqueUpToIso _ _
    (isBilimitBinaryBiconeOfIsSplitMonoOfCokernel (cokernelIsCokernel i))
  -- transport of the Hodge groups and of the hypercohomology along `e`
  have hterm : ∀ (p : ℕ) (j : ℤ),
      (Module.Finite Γ(T, ⊤) (Hc h (single0 h (K.X p)) j) ↔
        Module.Finite Γ(T, ⊤) (Hc h (single0 h ((L ⊞ cokernel i).X p)) j)) ∧
      Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X p)) j) =
        Module.finrank Γ(T, ⊤) (Hc h (single0 h ((L ⊞ cokernel i).X p)) j) := by
    intro p j
    have i₁ := finite_and_finrank_hypSheafFunctor h (K.X p) j
    have i₂ := finite_and_finrank_hypSheafFunctor h ((L ⊞ cokernel i).X p) j
    let e' : (hypSheafFunctor h j).obj (K.X p) ≃ₗ[Γ(T, ⊤)]
        (hypSheafFunctor h j).obj ((L ⊞ cokernel i).X p) :=
      ((hypSheafFunctor h j).mapIso ((HomologicalComplex.eval _ _ p).mapIso e)).toLinearEquiv
    refine ⟨⟨fun hK => i₂.1.2 (have := i₁.1.1 hK; Module.Finite.equiv e'),
      fun hK => i₁.1.2 (have := i₂.1.1 hK; Module.Finite.equiv e'.symm)⟩, ?_⟩
    exact i₁.2.trans (e'.finrank_eq.trans i₂.2.symm)
  let eH : (hypComplexFunctor h k).obj K ≃ₗ[Γ(T, ⊤)] (hypComplexFunctor h k).obj (L ⊞ cokernel i) :=
    ((hypComplexFunctor h k).mapIso e).toLinearEquiv
  have hH := eH.finrank_eq
  rw [hypComplexFunctor_obj, hypComplexFunctor_obj] at hH
  refine (finrank_hyp_eq_sum_of_biprod h hT L (cokernel i) k
    (fun p hp => (hterm p _).1.1 (hfin p hp)) ?_).1
  rw [← hH, heq]
  exact Finset.sum_congr rfl fun p _ => (hterm p _).2

end Summand

end MMP.FourfoldProofs.FractionalLogComplexProof
