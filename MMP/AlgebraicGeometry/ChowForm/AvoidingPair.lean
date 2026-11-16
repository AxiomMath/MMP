module

public import MMP.AlgebraicGeometry.ChowForm.CoreSkeleton
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Modules.FiniteLocallyFreeRankOne

/-!
# The avoiding pair and the closed fibre Chow form

Auxiliary declarations for the Chow form of a proper flat family of curves
(`MMP.Chow.DeterminantCurveForm`).

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3
-/

@[expose] public section

universe u

namespace MMP.Chow.DeterminantCurveForm

open MMP CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Defs

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} {N : ℕ}

section CoreLemmas

attribute [local instance] LocalFreeData.isOpenImmersion LocalFreeData.isAffine
  LocalFreeData.isDomain LocalFreeData.isNoetherian LocalFreeData.isIntegrallyClosed
  LocalFreeData.locFT

attribute [local instance] KoszulFamily.invertible

/-- The matrices `X₁ j` of the local free data of a `KoszulFamily` are the matrices of
multiplication by the coordinate section `x_j` on `V₁`, transported along `W.topIso`. -/
theorem KoszulFamily.toLocalFreeData_X₁ {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
    (F : KoszulFamily g π q d s) (hS : Mori.IsNormalVariety k sS) (j : Fin (N + 1)) :
    (F.toLocalFreeData hS).X₁ j =
      (F.data.matrix₁ (coordSection g q j)).map (F.data.W.topIso.inv).hom := rfl

/-- The matrices `X₀ j` of the local free data of a `KoszulFamily` are the matrices of
multiplication by the coordinate section `x_j` on `V₀`, transported along `W.topIso`. -/
theorem KoszulFamily.toLocalFreeData_X₀ {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
    (F : KoszulFamily g π q d s) (hS : Mori.IsNormalVariety k sS) (j : Fin (N + 1)) :
    (F.toLocalFreeData hS).X₀ j =
      (F.data.matrix₀ (coordSection g q j)).map (F.data.W.topIso.inv).hom := rfl

/-! #### The avoiding pair on the fibre -/

section AvoidFibre

/-- The section `ℓ_a = ∑ⱼ aⱼ xⱼ` of `H` attached to the linear form `∑ⱼ aⱼ Xⱼ`. -/
noncomputable def linSection (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {𝒞 : Scheme.{u}} (q : 𝒞 ⟶ Y) (a : Fin (N + 1) → k) : Γ(hyperplaneBundle g q, ⊤) :=
  ∑ j, (q ≫ g).appTop (Stacks.ProjectiveSpace.Cohomology.coeffToGlobalSections k N (a j)) •
    coordSection g q j

/-- The section `ℓ_a` is the pullback along `q ≫ g` of the degree-one section of `𝒪(1)` given by
the linear form `linForm a`. -/
theorem linSection_eq (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) {𝒞 : Scheme.{u}}
    (q : 𝒞 ⟶ Y) (a : Fin (N + 1) → k) :
    linSection g q a = (pullbackGlobalSections (q ≫ g)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)).hom
      (ProjectiveSpectrum.Proj.degreeSection (polyGrading k N) 1 ⟨_, linForm_mem a⟩) := by
  have h := congrArg
    (fun z : Stacks.ProjectiveSpace.Cohomology.twistSectionsModule k N ((1 : ℕ) : ℤ) =>
      (pullbackGlobalSections (q ≫ g)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)).hom z)
    (degreeSection_linForm (k := k) (N := N) a)
  refine Eq.trans ?_ h.symm
  erw [pullbackGlobalSections_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (pullbackGlobalSections_smul (q ≫ g) _ _ _).symm

/-- The section `ℓ_a` does not vanish at `y` when the linear form `linForm a` is not in the
homogeneous ideal of the image of `y` in `ℙᴺ`. -/
theorem mem_nonvanishingLocus_linSection
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) {𝒞 : Scheme.{u}} (q : 𝒞 ⟶ Y)
    (a : Fin (N + 1) → k) (y : 𝒞) (hy : linForm a ∉ ((q ≫ g) y).asHomogeneousIdeal) :
    y ∈ Stacks.Ample.nonvanishingLocus (hyperplaneBundle g q) (linSection g q a) := by
  rw [linSection_eq]
  exact Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections _ _ _
    (mem_nonvanishingLocus_degreeSection_one ⟨_, linForm_mem a⟩ _ hy)

/-- On direct image sections over `W`, multiplication by a combination `∑ⱼ cⱼ τⱼ` is the
combination `∑ⱼ c̄ⱼ` of the multiplications by `τⱼ`, where `c̄ⱼ` on `W` pulls back to the
restriction of `cⱼ`. -/
theorem directImageSectionsMap_coordMul_sum {𝒞 S : Scheme.{u}} (π : 𝒞 ⟶ S) (W : S.Opens)
    (H A : 𝒞.Modules) [Stacks.Ample.IsInvertibleModule 𝒞 H] [Stacks.Ample.IsInvertibleModule 𝒞 A]
    (n : ℕ) (m : ℤ) {ι : Type*} [Fintype ι] (c : ι → Γ(𝒞, ⊤)) (cbar : ι → Γ(S, W))
    (hc : ∀ j, 𝒞.presheaf.map (homOfLE (le_top : π ⁻¹ᵁ W ≤ ⊤)).op (c j) = π.app W (cbar j))
    (τ : ι → Γ(H, ⊤)) :
    MMP.Chow.directImageSectionsMap π W (MMP.Chow.coordMul H A (∑ j, c j • τ j) n m) =
      ∑ j, cbar j • MMP.Chow.directImageSectionsMap π W (MMP.Chow.coordMul H A (τ j) n m) := by
  ext s
  rw [LinearMap.sum_apply]
  refine (coordMul_app_sum H A c τ n m (π ⁻¹ᵁ W) s).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, hc j]
  rfl

/-- A constant of `k`, restricted to an open `W` of a `k`-scheme. -/
noncomputable def constOn {S : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (W : S.Opens) (a : k) :
    Γ(S, W) :=
  S.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (((Scheme.ΓSpecIso (.of k)).inv ≫ sS.appTop).hom a)

/-- Over an open `W` of the base, multiplication by `ℓ_a = ∑ⱼ aⱼ xⱼ` on the direct images is the
combination, with the constants `aⱼ`, of the multiplications by the coordinates `xⱼ`. -/
theorem directImageSectionsMap_coordMul_linSection {S 𝒞 : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY) (W : S.Opens) (A : 𝒞.Modules)
    [Stacks.Ample.IsInvertibleModule 𝒞 A] (n : ℕ) (m : ℤ) (a : Fin (N + 1) → k) :
    MMP.Chow.directImageSectionsMap π W
        (MMP.Chow.coordMul (hyperplaneBundle g q) A (linSection g q a) n m) =
      ∑ j, constOn sS W (a j) • MMP.Chow.directImageSectionsMap π W
        (MMP.Chow.coordMul (hyperplaneBundle g q) A (coordSection g q j) n m) := by
  refine directImageSectionsMap_coordMul_sum π W _ A n m (fun j => (q ≫ g).appTop
    (Stacks.ProjectiveSpace.Cohomology.coeffToGlobalSections k N (a j))) _ (fun j => ?_)
    (coordSection g q)
  have h1 : (Scheme.ΓSpecIso (.of k)).inv ≫ (projToSpecCoeff k N).appTop ≫ (q ≫ g).appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sS.appTop ≫ π.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, Category.assoc, hgY, ← hπq]
  have h2 := Scheme.Hom.naturality π (homOfLE (le_top : W ≤ ⊤)).op
  have h3 := congrArg (fun φ => φ.hom (((Scheme.ΓSpecIso (.of k)).inv ≫ sS.appTop).hom (a j))) h2
  have h4 := congrArg (fun φ => φ.hom (a j)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  change 𝒞.presheaf.map _ ((q ≫ g).appTop.hom
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (projToSpecCoeff k N).appTop).hom (a j))) = _
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [h4]
  exact h3.symm

/-- Evaluating the constant `a` on `W` at a point `x` of `W` gives the image of `a` in the
residue field at `x`. -/
theorem Γevaluation_topIso_inv_constOn {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (W : S.Opens) (x : W.toScheme) (a : k) :
    (W.toScheme.Γevaluation x).hom ((W.topIso.inv).hom (constOn sS W a)) =
      kEval (W.ι ≫ sS) x a := by
  have key : S.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ W.topIso.inv = W.ι.appTop := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop]
    exact (S.presheaf.map_comp _ _).symm.trans (congrArg S.presheaf.map (Subsingleton.elim _ _))
  exact congrArg (fun φ => (W.toScheme.Γevaluation x).hom
    (φ.hom (((Scheme.ΓSpecIso (.of k)).inv ≫ sS.appTop).hom a))) key

/-- Injectivity and exactness of a pair of matrices survive an isomorphism of the coefficient
fields. -/
theorem exact_map_of_bijective {K L : Type*} [CommRing K] [CommRing L] (ε : K →+* L)
    (hε : Function.Bijective ε) {α β γ : Type*} [Fintype α] [Fintype β]
    {A : Matrix α β K} {B : Matrix γ α K}
    (h : Function.Injective A.mulVec ∧ ∀ v, B.mulVec v = 0 → ∃ w, A.mulVec w = v) :
    Function.Injective (A.map ε).mulVec ∧
      ∀ v, (B.map ε).mulVec v = 0 → ∃ w, (A.map ε).mulVec w = v := by
  let e := RingEquiv.ofBijective ε hε
  have hA : ∀ v, (A.map ε).mulVec (ε ∘ v) = ε ∘ A.mulVec v :=
    fun v => funext fun i => (RingHom.map_mulVec ε A v i).symm
  have hB : ∀ v, (B.map ε).mulVec (ε ∘ v) = ε ∘ B.mulVec v :=
    fun v => funext fun i => (RingHom.map_mulVec ε B v i).symm
  constructor
  · intro v v' hvv
    obtain ⟨u, rfl⟩ : ∃ u, ε ∘ u = v := ⟨e.symm ∘ v, funext fun _ => e.apply_symm_apply _⟩
    obtain ⟨u', rfl⟩ : ∃ u, ε ∘ u = v' := ⟨e.symm ∘ v', funext fun _ => e.apply_symm_apply _⟩
    rw [hA, hA] at hvv
    rw [h.1 (hε.1.comp_left hvv)]
  · intro v hv
    obtain ⟨u, rfl⟩ : ∃ u, ε ∘ u = v := ⟨e.symm ∘ v, funext fun _ => e.apply_symm_apply _⟩
    rw [hB] at hv
    have h0 : ε ∘ B.mulVec u = ε ∘ (0 : γ → K) := by
      rw [hv]
      funext i
      simp
    obtain ⟨w, hw⟩ := h.2 u (hε.1.comp_left h0)
    exact ⟨ε ∘ w, by rw [hA, hw]⟩

/-- Evaluation at a point `x` of the open subscheme `W` factors through the germ and residue map of
`S` at the image of `x`, followed by the residue field map of the inclusion `W.ι`. -/
theorem topIso_inv_Γevaluation {S : Scheme.{u}} (W : S.Opens) (x : W.toScheme) :
    W.topIso.inv ≫ W.toScheme.Γevaluation x =
      (S.presheaf.germ W (W.ι x) (show W.ι x ∈ W from x.2) ≫ S.residue (W.ι x)) ≫
        W.ι.residueFieldMap x := by
  have h1 : W.toScheme.Γevaluation x =
      W.toScheme.presheaf.germ ⊤ x (show x ∈ (⊤ : W.toScheme.Opens) from Set.mem_univ x) ≫
        W.toScheme.residue x := rfl
  rw [h1, Category.assoc, Scheme.residue_residueFieldMap, Scheme.Hom.germ_stalkMap_assoc]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← W.toScheme.presheaf.germ_res (homOfLE (le_top : W.ι ⁻¹ᵁ W ≤ ⊤)) x x.2,
    ← Category.assoc]
  congr 1
  rw [Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
  exact (S.presheaf.map_comp _ _).symm.trans (congrArg S.presheaf.map (Subsingleton.elim _ _))

/-- The residue field map of the inclusion of an open subscheme is bijective. -/
theorem bijective_residueFieldMap_ι {S : Scheme.{u}} (W : S.Opens) (x : W.toScheme) :
    Function.Bijective (W.ι.residueFieldMap x).hom :=
  ConcreteCategory.bijective_of_isIso (W.ι.residueFieldMap x)

end AvoidFibre

/-- For a proper flat family of curves `π : 𝒞 → S` over a normal variety whose closed fibres have
degree `d`, every point `s` of `S` admits a `KoszulFamily`. -/
theorem exists_koszulFamily {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d)
    (hdeg : haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
      ∀ s : S, IsClosed ({s} : Set S) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc g sS π q s) = d)
    (s : S) : Nonempty (KoszulFamily g π q d s) := by
  haveI : IsIntegral S := hS.1.toIsIntegral
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  haveI : QuasiCompact sS := hS.1.toQuasiCompact
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  haveI : AlgebraicGeometry.IsNoetherian S := AlgebraicGeometry.IsNoetherian.mk
  obtain ⟨A, hAinv, hA⟩ := exists_relativelyAmple sS sY hY π q hπq
  haveI := hAinv
  haveI : IsLocallyNoetherian 𝒞 := LocallyOfFiniteType.isLocallyNoetherian π
  let H : 𝒞.Modules := hyperplaneBundle g q
  let mm : Fin 3 → ℤ := ![-2 + 1 + 1, -2 + 1, -2]
  haveI hFinv : ∀ j, Stacks.Ample.IsInvertibleModule 𝒞 (Stacks.Ample.tensorPowModule 𝒞 H (mm j)) :=
    fun j => Stacks.Ample.isInvertibleModule_tensorPowModule 𝒞 H (mm j)
  haveI hFcoh : ∀ j, (Stacks.Ample.tensorPowModule 𝒞 H (mm j)).IsCoherent := fun j =>
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible 𝒞 _
  have hflat : ∀ (j : Fin 3) (n : ℕ), IsFlatOver π.toLRSHom.toShHom
      (Stacks.RelativeVeryAmple.tensorModules 𝒞 (Stacks.Ample.tensorPowModule 𝒞 H (mm j))
        (Stacks.Ample.tensorPowModule 𝒞 A (n : ℤ))) := fun j n =>
    MMP.Chow.isFlatOver_tensorModules_tensorPowModule π
      (fun j => Stacks.Ample.tensorPowModule 𝒞 H (mm j)) A j n
  obtain ⟨n₁, hn₁⟩ :=
    MMP.Chow.exists_forall_isZero_higherDirectImage_and_isFiniteLocallyFree_and_isIso_baseChange
      π A hA (fun j : Fin 3 => Stacks.Ample.tensorPowModule 𝒞 H (mm j)) hflat
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨n₂, hn₂⟩ := exists_vanishing_twists π H A hA hV mm
  let n := max n₁ n₂
  have hn₁' := fun j => hn₁ n (le_max_left _ _) j
  have key : ∀ j : Fin 3, ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ, ∀ V' : S.Opens, IsAffineOpen V' → V' ≤ U →
      Nonempty (Module.Basis (Fin r) Γ(S, V')
        Γ((Scheme.Modules.pushforward π).obj (MMP.Chow.twistMod H A n (mm j)), V')) := fun j => by
    have hfl := (hn₁' j).2.1
    haveI := hfl
    haveI : ((Scheme.Modules.pushforward π).obj (MMP.Chow.twistMod H A n (mm j))).IsQuasicoherent :=
      isQuasicoherent_ringSheaf _
    exact exists_forall_basis_of_isFiniteLocallyFree _ hfl s
  choose U hsU r hb using key
  obtain ⟨W, hW, hsW, hWle⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (U := V ⊓ U 0 ⊓ U 1 ⊓ U 2) (x := s)
    (show s ∈ V ⊓ U 0 ⊓ U 1 ⊓ U 2 from ⟨⟨⟨hsV, hsU 0⟩, hsU 1⟩, hsU 2⟩)
  have hWV : W ≤ V := fun y hy => (hWle hy).1.1.1
  have hWU : ∀ j : Fin 3, W ≤ U j := by
    intro j y hy
    fin_cases j
    · exact (hWle hy).1.1.2
    · exact (hWle hy).1.2
    · exact (hWle hy).2
  let b : ∀ j : Fin 3, Module.Basis (Fin (r j)) Γ(S, W)
      Γ((Scheme.Modules.pushforward π).obj (MMP.Chow.twistMod H A n (mm j)), W) :=
    fun j => (hb j W hW (hWU j)).some
  let data : MMP.Chow.KoszulSheafData π H A n :=
    { W := W, r₀ := r 0, r₁ := r 1, r₂ := r 2, b₀ := b 0, b₁ := b 1, b₂ := b 2 }
  haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  obtain ⟨x, hxW, hxc⟩ : ∃ x ∈ W, IsClosed ({x} : Set S) := by
    obtain ⟨x, hx1, hx2⟩ := nonempty_inter_closedPoints (X := S) (Z := (W : Set S)) ⟨s, hsW⟩
      W.isOpen.isLocallyClosed
    exact ⟨x, hx1, hx2⟩
  haveI hinv : ∀ j, Stacks.Ample.IsInvertibleModule 𝒞 (MMP.Chow.twistMod H A n (mm j)) := fun j =>
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules 𝒞
      (Stacks.Ample.tensorPowModule 𝒞 H (mm j)) (Stacks.Ample.tensorPowModule 𝒞 A (n : ℤ))
  have hvanW := fun j => vanishing_of_le π hV hW hWV (MMP.Chow.twistMod H A n (mm j)) (hinv j)
    (hn₂ n (le_max_right _ _) j)
  have hfib := fun j => fibre_cohomology_of_basis π hW (MMP.Chow.twistMod H A n (mm j)) (hinv j)
    (hvanW j) (b j) x hxW
  haveI hLinv := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N
  have hψ : π ≫ sS = (q ≫ g) ≫ projToSpecCoeff k N := by rw [hπq, Category.assoc, hgY]
  have hbij := kEval_bijective sS x hxc
  have hsX := fiber_structure_eq sS π x
  have hdeg' := hdeg x hxc
  have hrank : ∀ (m : ℤ) (j j' : Fin 3), mm j = m → mm j' = m + 1 →
      (r j' : ℤ) - r j = d := by
    intro m j j' hj hj'
    have h1 := finrank_diff_fibre sS (projToSpecCoeff k N) π (q ≫ g) hψ
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) A n m x (hdim x hxc).le
      (kEval sS x) hbij hsX (hj ▸ (hfib j).1) (hj' ▸ (hfib j').1)
    rw [← hj', ← hj, (hfib j).2, (hfib j').2] at h1
    exact h1.trans hdeg'
  have hr0 : (r 0 : ℤ) - r 1 = d := hrank (-2 + 1) 1 0 rfl rfl
  have hr1 : (r 1 : ℤ) - r 2 = d := hrank (-2) 2 1 rfl rfl
  refine ⟨{
    A := A
    invertible := hAinv
    n := n
    ample := hA
    uniform := ?_
    data := data
    mem := hsW
    affine := hW
    rank₀ := ?_
    rank₁ := ?_
    vanishing := ?_ }⟩
  · refine ⟨?_, ?_⟩
    · intro m hm i hi
      rcases hm with rfl | rfl | rfl
      · exact (hn₁' 2).1 i hi
      · exact (hn₁' 1).1 i hi
      · exact (hn₁' 0).1 i hi
    · intro m hm X' S' g' f' g'' hsq
      rcases hm with rfl | rfl | rfl
      · exact (hn₁' 2).2.2 g' f' g'' hsq
      · exact (hn₁' 1).2.2 g' f' g'' hsq
      · exact (hn₁' 0).2.2 g' f' g'' hsq
  · show r 0 = r 1 + d
    omega
  · show r 1 = r 2 + d
    omega
  · intro m hm p hp
    rcases hm with rfl | rfl | rfl
    · exact hvanW 2 p hp
    · exact hvanW 1 p hp
    · exact hvanW 0 p hp

/-- At a pair of hyperplanes `(a, b)`, the specialized universal hyperplane `ℓ_u : V₂ → V₁` is
`∑ a_j X₁ j` evaluated at `x`. -/
theorem LocalFreeData.ellU₁_map_evalPt {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
    (D : LocalFreeData g sS π q d s) (x : D.U) (a b : Fin (N + 1) → k) :
    D.ellU₁.map (D.evalPt x a b) =
      ∑ j, kEval (D.ι ≫ sS) x (a j) • (D.X₁ j).map (D.U.Γevaluation x).hom := by
  ext i l
  simp [LocalFreeData.ellU₁, LocalFreeData.evalPt, Matrix.sum_apply]

/-- At a pair of hyperplanes `(a, b)`, the specialized universal hyperplane `ℓ_v : V₂ → V₁` is
`∑ b_j X₁ j` evaluated at `x`. -/
theorem LocalFreeData.ellV₁_map_evalPt {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
    (D : LocalFreeData g sS π q d s) (x : D.U) (a b : Fin (N + 1) → k) :
    D.ellV₁.map (D.evalPt x a b) =
      ∑ j, kEval (D.ι ≫ sS) x (b j) • (D.X₁ j).map (D.U.Γevaluation x).hom := by
  ext i l
  simp [LocalFreeData.ellV₁, LocalFreeData.evalPt, Matrix.sum_apply]

/-- At a pair of hyperplanes `(a, b)`, the specialized universal hyperplane `ℓ_u : V₁ → V₀` is
`∑ a_j X₀ j` evaluated at `x`. -/
theorem LocalFreeData.ellU₀_map_evalPt {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
    (D : LocalFreeData g sS π q d s) (x : D.U) (a b : Fin (N + 1) → k) :
    D.ellU₀.map (D.evalPt x a b) =
      ∑ j, kEval (D.ι ≫ sS) x (a j) • (D.X₀ j).map (D.U.Γevaluation x).hom := by
  ext i l
  simp [LocalFreeData.ellU₀, LocalFreeData.evalPt, Matrix.sum_apply]

/-- At a pair of hyperplanes `(a, b)`, the specialized universal hyperplane `ℓ_v : V₁ → V₀` is
`∑ b_j X₀ j` evaluated at `x`. -/
theorem LocalFreeData.ellV₀_map_evalPt {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
    (D : LocalFreeData g sS π q d s) (x : D.U) (a b : Fin (N + 1) → k) :
    D.ellV₀.map (D.evalPt x a b) =
      ∑ j, kEval (D.ι ≫ sS) x (b j) • (D.X₀ j).map (D.U.Γevaluation x).hom := by
  ext i l
  simp [LocalFreeData.ellV₀, LocalFreeData.evalPt, Matrix.sum_apply]

/-- For a `KoszulFamily`, the specialization at `x` of the matrix of multiplication by the linear
section `ℓ_e` is the `e`-weighted sum of the specialized matrices of the coordinate sections. -/
theorem KoszulFamily.sum_smul_toMatrix_coordMul_map {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (hS : Mori.IsNormalVariety k sS)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY) {d : ℕ} {s : S}
    (F : KoszulFamily g π q d s) (x : (F.toLocalFreeData hS).U) (e : Fin (N + 1) → k) (m : ℤ)
    {rr rr' : ℕ} (bb : Module.Basis (Fin rr) Γ(S, F.data.W) (MMP.Chow.directImageSections π
      F.data.W (MMP.Chow.twistMod (hyperplaneBundle g q) F.A F.n m)))
    (bb' : Module.Basis (Fin rr') Γ(S, F.data.W) (MMP.Chow.directImageSections π
      F.data.W (MMP.Chow.twistMod (hyperplaneBundle g q) F.A F.n (m + 1)))) :
    ∑ j, kEval ((F.toLocalFreeData hS).ι ≫ sS) x (e j) • (LinearMap.toMatrix bb bb'
        (MMP.Chow.directImageSectionsMap π F.data.W (MMP.Chow.coordMul (hyperplaneBundle g q)
          F.A (coordSection g q j) F.n m))).map
        (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp (F.data.W.topIso.inv).hom) =
      (LinearMap.toMatrix bb bb' (MMP.Chow.directImageSectionsMap π F.data.W
        (MMP.Chow.coordMul (hyperplaneBundle g q) F.A (linSection g q e) F.n m))).map
        (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp (F.data.W.topIso.inv).hom) := by
  have hE'k : ∀ c : k, (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp
      (F.data.W.topIso.inv).hom) (constOn sS F.data.W c) =
        kEval ((F.toLocalFreeData hS).ι ≫ sS) x c :=
    Γevaluation_topIso_inv_constOn sS F.data.W x
  rw [directImageSectionsMap_coordMul_linSection sS sY g hgY π q hπq F.data.W F.A F.n m e,
    map_sum]
  ext i l
  simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, map_sum,
    smul_eq_mul, map_mul, hE'k]

/-- For a `KoszulFamily`, the first Koszul differential specialized at `(x, a, b)` is
`w ↦ (-ℓ_b w, ℓ_a w)`, with `ℓ_a`, `ℓ_b` the multiplications by the linear sections on `V₂`. -/
theorem KoszulFamily.A_map_evalPt {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (hS : Mori.IsNormalVariety k sS)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY) {d : ℕ} {s : S}
    (F : KoszulFamily g π q d s) (x : (F.toLocalFreeData hS).U) (a b : Fin (N + 1) → k) :
    (F.toLocalFreeData hS).A.map ((F.toLocalFreeData hS).evalPt x a b) = Matrix.fromRows
      (-((LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π F.data.W
        (MMP.Chow.coordMul (hyperplaneBundle g q) F.A (linSection g q b) F.n (-2)))).map
          (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp (F.data.W.topIso.inv).hom)))
      ((LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π F.data.W
        (MMP.Chow.coordMul (hyperplaneBundle g q) F.A (linSection g q a) F.n (-2)))).map
          (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp (F.data.W.topIso.inv).hom)) := by
  have hX : ∀ j, ((F.toLocalFreeData hS).X₁ j).map ((F.toLocalFreeData hS).U.Γevaluation x).hom =
      (LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π F.data.W
        (MMP.Chow.coordMul (hyperplaneBundle g q) F.A (coordSection g q j) F.n (-2)))).map
          (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp (F.data.W.topIso.inv).hom) :=
    fun j => by
      rw [KoszulFamily.toLocalFreeData_X₁]
      ext i l
      rfl
  rw [LocalFreeData.A_map_ring, LocalFreeData.ellU₁_map_evalPt, LocalFreeData.ellV₁_map_evalPt,
    ← KoszulFamily.sum_smul_toMatrix_coordMul_map sS sY hS g hgY π q hπq F x,
    ← KoszulFamily.sum_smul_toMatrix_coordMul_map sS sY hS g hgY π q hπq F x]
  simp only [hX]
  rfl

/-- For a `KoszulFamily`, the second Koszul differential specialized at `(x, a, b)` is
`(s, t) ↦ ℓ_a s + ℓ_b t`, with `ℓ_a`, `ℓ_b` the multiplications by the linear sections on `V₁`. -/
theorem KoszulFamily.B_map_evalPt {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (hS : Mori.IsNormalVariety k sS)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY) {d : ℕ} {s : S}
    (F : KoszulFamily g π q d s) (x : (F.toLocalFreeData hS).U) (a b : Fin (N + 1) → k) :
    (F.toLocalFreeData hS).B.map ((F.toLocalFreeData hS).evalPt x a b) = Matrix.fromCols
      ((LinearMap.toMatrix F.data.b₁ F.data.b₀ (MMP.Chow.directImageSectionsMap π F.data.W
        (MMP.Chow.coordMul (hyperplaneBundle g q) F.A (linSection g q a) F.n (-2 + 1)))).map
          (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp (F.data.W.topIso.inv).hom))
      ((LinearMap.toMatrix F.data.b₁ F.data.b₀ (MMP.Chow.directImageSectionsMap π F.data.W
        (MMP.Chow.coordMul (hyperplaneBundle g q) F.A (linSection g q b) F.n (-2 + 1)))).map
          (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp (F.data.W.topIso.inv).hom)) := by
  have hX : ∀ j, ((F.toLocalFreeData hS).X₀ j).map ((F.toLocalFreeData hS).U.Γevaluation x).hom =
      (LinearMap.toMatrix F.data.b₁ F.data.b₀ (MMP.Chow.directImageSectionsMap π F.data.W
        (MMP.Chow.coordMul (hyperplaneBundle g q) F.A (coordSection g q j) F.n (-2 + 1)))).map
          (((F.toLocalFreeData hS).U.Γevaluation x).hom.comp (F.data.W.topIso.inv).hom) :=
    fun j => by
      rw [KoszulFamily.toLocalFreeData_X₀]
      ext i l
      rfl
  rw [LocalFreeData.B_map_ring, LocalFreeData.ellU₀_map_evalPt, LocalFreeData.ellV₀_map_evalPt,
    ← KoszulFamily.sum_smul_toMatrix_coordMul_map sS sY hS g hgY π q hπq F x,
    ← KoszulFamily.sum_smul_toMatrix_coordMul_map sS sY hS g hgY π q hπq F x]
  simp only [hX]
  rfl

set_option maxRecDepth 20000 in
/-- For the local free data of a `KoszulFamily`, at a closed point `x` of `W` and a pair of
hyperplanes `(a, b)` missing the image of the fibre, the specialized map `V₂ → V₁ ⊕ V₁`,
`w ↦ (-ℓ_b w, ℓ_a w)`, is injective and its image is the kernel of `(s, t) ↦ ℓ_a s + ℓ_b t`. -/
theorem koszulFamily_exact_of_avoid_aux {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d) {s : S} (F : KoszulFamily g π q d s) :
    let D := F.toLocalFreeData hS
    ∀ x : D.U, IsClosed ({x} : Set D.U) → ∀ a b : Fin (N + 1) → k,
      AvoidsPair (fibreImage g π q D.ι x) a b →
        Function.Injective (D.A.map (D.evalPt x a b)).mulVec ∧
        ∀ v, (D.B.map (D.evalPt x a b)).mulVec v = 0 →
          ∃ w, (D.A.map (D.evalPt x a b)).mulVec w = v := by
  intro D x hx a b hab
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set W := F.data.W
  let H := hyperplaneBundle g q
  set t : S := W.ι x
  have ht : t ∈ W := x.2
  -- the specialization at `x` is the reduction at `t`, up to the isomorphism of residue fields
  let ε := (W.ι.residueFieldMap x).hom
  have hε : Function.Bijective ε := bijective_residueFieldMap_ι W x
  have hE : ∀ {r r' : ℕ} (M : Matrix (Fin r) (Fin r') Γ(S, W)),
      M.map ((D.U.Γevaluation x).hom.comp (W.topIso.inv).hom) =
        (M.map (residueOfMem t ht).hom).map ε := by
    intro r r' M
    have h := congrArg CommRingCat.Hom.hom (topIso_inv_Γevaluation W x)
    ext i l
    exact RingHom.congr_fun h (M i l)
  -- the twists and the multiplications by `ℓ_a`, `ℓ_b`
  let σa := linSection g q a
  let σb := linSection g q b
  haveI hinv : ∀ m : ℤ, Stacks.Ample.IsInvertibleModule 𝒞 (MMP.Chow.twistMod H F.A F.n m) :=
    fun m => Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules 𝒞
      (Stacks.Ample.tensorPowModule 𝒞 H m) (Stacks.Ample.tensorPowModule 𝒞 F.A (F.n : ℤ))
  let g' := fiberιOfMem π t ht
  let ι' := (π ⁻¹ᵁ W).ι
  have hg'ι : ∀ y, ι' (g' y) = π.fiberι t y := fun y => by
    rw [← Scheme.Hom.comp_apply, fiberιOfMem_ι]
  let U : Γ(H, ⊤) → (π.fiber t).Opens := fun σ =>
    (g' ≫ ι') ⁻¹ᵁ ⟨Stacks.Ample.nonvanishingLocus H σ,
      Stacks.NonvanishingOpen.isOpen_nonvanishingLocus 𝒞 H σ⟩
  have hU : ∀ σ y, y ∈ U σ → ι' (g' y) ∈ Stacks.Ample.nonvanishingLocus H σ := fun σ y hy => hy
  have hbij : ∀ (σ : Γ(H, ⊤)) (m : ℤ) (y : π.fiber t), y ∈ U σ →
      Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map
        ((Scheme.Modules.pullback g').map ((Scheme.Modules.pullback ι').map
          (MMP.Chow.coordMul H F.A σ F.n m))).mapPresheaf) := fun σ m y hy =>
    bijective_stalk_pullback_map g' _ y (bijective_stalk_pullback_map ι' _ (g' y)
      (bijective_stalk_coordMul H F.A σ F.n m (hU σ y hy)))
  have hcov : (⊤ : (π.fiber t).Opens) ≤ U σa ⊔ U σb := by
    intro y _
    have hy : (q ≫ g) (ι' (g' y)) ∈ fibreImage g π q D.ι x := by
      rw [fibreImage_eq_range sS g π q D.ι x hx, hg'ι]
      exact ⟨y, rfl⟩
    have hno := hab _ hy
    by_cases h1 : linForm a ∈ ((q ≫ g) (ι' (g' y))).asHomogeneousIdeal
    · exact Or.inr (mem_nonvanishingLocus_linSection g q b _ fun h2 => hno ⟨h1, h2⟩)
    · exact Or.inl (mem_nonvanishingLocus_linSection g q a _ h1)
  have hcomm := MMP.Chow.coordMul_comm H F.A σb σa F.n (-2)
  have hglue := koszul_glue
    ((Scheme.Modules.pullback g').map ((Scheme.Modules.pullback ι').map
      (MMP.Chow.coordMul H F.A σa F.n (-2))))
    ((Scheme.Modules.pullback g').map ((Scheme.Modules.pullback ι').map
      (MMP.Chow.coordMul H F.A σb F.n (-2))))
    ((Scheme.Modules.pullback g').map ((Scheme.Modules.pullback ι').map
      (MMP.Chow.coordMul H F.A σa F.n (-2 + 1))))
    ((Scheme.Modules.pullback g').map ((Scheme.Modules.pullback ι').map
      (MMP.Chow.coordMul H F.A σb F.n (-2 + 1))))
    (by simp only [← Functor.map_comp, hcomm]) (U σa) (U σb) hcov
    (fun y hy => hbij σa (-2) y hy) (fun y hy => hbij σa (-2 + 1) y hy)
    (fun y hy => hbij σb (-2) y hy) (fun y hy => hbij σb (-2 + 1) y hy)
  have hfib := fibre_koszul π F.affine (MMP.Chow.twistMod H F.A F.n (-2))
    (MMP.Chow.twistMod H F.A F.n (-2 + 1)) (MMP.Chow.twistMod H F.A F.n (-2 + 1 + 1))
    (hinv _) (hinv _) (hinv _)
    (F.vanishing _ (Or.inl rfl)) (F.vanishing _ (Or.inr (Or.inl rfl)))
    (F.vanishing _ (Or.inr (Or.inr rfl))) F.data.b₂ F.data.b₁ F.data.b₀
    (MMP.Chow.coordMul H F.A σa F.n (-2)) (MMP.Chow.coordMul H F.A σb F.n (-2))
    (MMP.Chow.coordMul H F.A σa F.n (-2 + 1)) (MMP.Chow.coordMul H F.A σb F.n (-2 + 1)) t ht
    hglue.1 hglue.2
  have hfin := exact_map_of_bijective ε hε hfib
  rw [KoszulFamily.A_map_evalPt sS sY hS g hgY π q hπq F x a b,
    KoszulFamily.B_map_evalPt sS sY hS g hgY π q hπq F x a b, hE, hE, hE, hE]
  rwa [Matrix.fromRows_map, Matrix.fromCols_map, Matrix.map_neg _ (map_neg ε)] at hfin

/-- For the local free data of a `KoszulFamily`, at a closed point `x` of `W` and a pair of
hyperplanes `(a, b)` of `ℙᴺ` missing the image of the fibre, the Koszul complex
`V₂ → V₁ ⊕ V₁ → V₀` specialized at `(x, a, b)` is split exact. -/
theorem koszulFamily_exact_of_avoid {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d) {s : S} (F : KoszulFamily g π q d s) :
    let D := F.toLocalFreeData hS
    ∀ x : D.U, IsClosed ({x} : Set D.U) → ∀ a b : Fin (N + 1) → k,
      AvoidsPair (fibreImage g π q D.ι x) a b →
        MMP.Chow.IsSplitExact D.e (D.A.map (D.evalPt x a b)) (D.B.map (D.evalPt x a b)) := by
  intro D x hx a b hab
  obtain ⟨hinj, hex⟩ :=
    koszulFamily_exact_of_avoid_aux sS sY hS hY g hg hgY π q hπq hdim d hd F x hx a b hab
  refine isSplitExact_of_injective_of_ker_le D.e ?_ hinj hex
  rw [← Matrix.map_mul, D.B_mul_A]
  simp

/-- Over a local ring, an element of the maximal ideal acts nilpotently on a module of finite
length (Nakayama on the stable image of its powers). -/
theorem exists_pow_smul_eq_zero_of_isArtinian {L M : Type*} [CommRing L] [IsLocalRing L]
    [AddCommGroup M] [Module L M] [IsArtinian L M] [IsNoetherian L M] (t : L)
    (ht : t ∈ IsLocalRing.maximalIdeal L) : ∃ n : ℕ, ∀ m : M, t ^ n • m = 0 := by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M t
  set N := LinearMap.range (t ^ n • LinearMap.id : M →ₗ[L] M)
  have hle : N ≤ Ideal.span {t} • N := by
    intro x hx
    obtain ⟨y, rfl⟩ : x ∈ LinearMap.range (t ^ (n + 1) • LinearMap.id : M →ₗ[L] M) :=
      hn (n + 1) (by omega) ▸ hx
    rw [show (t ^ (n + 1) • LinearMap.id : M →ₗ[L] M) y = t • (t ^ n • y) by
      simp [pow_succ', mul_smul]]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) ⟨y, by simp⟩
  have hbot : N = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
    (IsNoetherian.noetherian N) hle (by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact (Ideal.span_singleton_le_iff_mem _).2 ht)
  refine ⟨n, fun m => ?_⟩
  have : t ^ n • m ∈ N := ⟨m, by simp⟩
  rwa [hbot] at this

/-- Near any point `y` of `𝒞`, the multiplications by the coordinate sections `x_i` on the twists
`m → m + 1` and `m + 1 → m + 2` are all multiples `c i • P`, `c i • P'` of one pair of stalk
isomorphisms, with `c j₀ = 1` for some `j₀`. -/
theorem exists_stalk_coordMul_eq_smul {𝒞 : Scheme.{u}}
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (q : 𝒞 ⟶ Y) (A : 𝒞.Modules)
    [Stacks.Ample.IsInvertibleModule 𝒞 A] (n : ℕ) (m : ℤ) (y : 𝒞) :
    ∃ (j0 : Fin (N + 1)) (c : Fin (N + 1) → 𝒞.presheaf.stalk y), c j0 = 1 ∧
      ∃ (P : (MMP.Chow.twistMod (hyperplaneBundle g q) A n m).presheaf.stalk y ≃ₗ[
          𝒞.presheaf.stalk y]
            (MMP.Chow.twistMod (hyperplaneBundle g q) A n (m + 1)).presheaf.stalk y)
        (P' : (MMP.Chow.twistMod (hyperplaneBundle g q) A n (m + 1)).presheaf.stalk y ≃ₗ[
          𝒞.presheaf.stalk y]
            (MMP.Chow.twistMod (hyperplaneBundle g q) A n (m + 1 + 1)).presheaf.stalk y),
        (∀ i z, stalkLinearMap _ _
          (MMP.Chow.coordMul (hyperplaneBundle g q) A (coordSection g q i) n m) y z = c i • P z) ∧
          ∀ i z, stalkLinearMap _ _
            (MMP.Chow.coordMul (hyperplaneBundle g q) A (coordSection g q i) n (m + 1)) y z =
              c i • P' z := by
  let H := hyperplaneBundle g q
  obtain ⟨j0, hj0⟩ : ∃ j0, y ∈ Stacks.Ample.nonvanishingLocus H (coordSection g q j0) := by
    let p := (q ≫ g) y
    haveI : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
    obtain ⟨j, hj⟩ := exists_notMem_X (k := k) (N := N) (𝔭 := p.asHomogeneousIdeal.toIdeal)
      p.not_irrelevant_le
    exact ⟨j, Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections _ _ _
      (mem_nonvanishingLocus_degreeSection_one
        ⟨MvPolynomial.X j, (MvPolynomial.mem_homogeneousSubmodule _ _).2
          (MvPolynomial.isHomogeneous_X k j)⟩ p hj)⟩
  have hb := Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus H
    (coordSection g q j0) hj0
  exact ⟨j0, fun i => hb.coord ((H.presheaf.Γgerm y).hom (coordSection g q i)), hb.coord_self,
    LinearEquiv.ofBijective _ (bijective_stalk_coordMul H A _ n m hj0),
    LinearEquiv.ofBijective _ (bijective_stalk_coordMul H A _ n (m + 1) hj0),
    fun i z => stalk_coordMul_eq_coord_smul H A _ _ hj0 n m z,
    fun i z => stalk_coordMul_eq_coord_smul H A _ _ hj0 n (m + 1) z⟩

set_option maxRecDepth 20000 in
/-- For the local free data of a `KoszulFamily`, the Koszul complex over `R[u, v]` is exact at
`V₁ ⊕ V₁`: a pair `(s, t)` of sections of `V₁ ⊗ R[u, v]` with `ℓ_u s + ℓ_v t = 0` is
`(-ℓ_v w, ℓ_u w)` for a section `w` of `V₂ ⊗ R[u, v]`. -/
theorem koszulFamily_exact_middle {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d) {s : S} (F : KoszulFamily g π q d s) :
    let D := F.toLocalFreeData hS
    ∀ v, D.B.mulVec v = 0 → ∃ w, D.A.mulVec w = v := by
  intro D v hv
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set W := F.data.W
  let H := hyperplaneBundle g q
  let ι : Γ(D.U, ⊤) ≃+* Γ(S, W) := W.topIso.commRingCatIsoToRingEquiv
  let ψ : Fin (N + 1) → (MMP.Chow.twistMod H F.A F.n (-2) ⟶ MMP.Chow.twistMod H F.A F.n (-2 + 1)) :=
    fun j => MMP.Chow.coordMul H F.A (coordSection g q j) F.n (-2)
  let ψ' : Fin (N + 1) →
      (MMP.Chow.twistMod H F.A F.n (-2 + 1) ⟶ MMP.Chow.twistMod H F.A F.n (-2 + 1 + 1)) :=
    fun j => MMP.Chow.coordMul H F.A (coordSection g q j) F.n (-2 + 1)
  have hU₁ : D.ellU₁ = ∑ j, (MvPolynomial.X (Sum.inl j) : D.Pol) •
      ((LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π W (ψ j))).map
        ι.symm).map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) := by
    simp only [LocalFreeData.ellU₁, KoszulFamily.toLocalFreeData_X₁]
    rfl
  have hV₁ : D.ellV₁ = ∑ j, (MvPolynomial.X (Sum.inr j) : D.Pol) •
      ((LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π W (ψ j))).map
        ι.symm).map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) := by
    simp only [LocalFreeData.ellV₁, KoszulFamily.toLocalFreeData_X₁]
    rfl
  have hU₀ : D.ellU₀ = ∑ j, (MvPolynomial.X (Sum.inl j) : D.Pol) •
      ((LinearMap.toMatrix F.data.b₁ F.data.b₀ (MMP.Chow.directImageSectionsMap π W (ψ' j))).map
        ι.symm).map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) := by
    simp only [LocalFreeData.ellU₀, KoszulFamily.toLocalFreeData_X₀]
    rfl
  have hV₀ : D.ellV₀ = ∑ j, (MvPolynomial.X (Sum.inr j) : D.Pol) •
      ((LinearMap.toMatrix F.data.b₁ F.data.b₀ (MMP.Chow.directImageSectionsMap π W (ψ' j))).map
        ι.symm).map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) := by
    simp only [LocalFreeData.ellV₀, KoszulFamily.toLocalFreeData_X₀]
    rfl
  have hcomp : IsCompact ((π ⁻¹ᵁ W : 𝒞.Opens) : Set 𝒞) :=
    QuasiCompact.isCompact_preimage (f := π) (U := (W : Set S)) W.isOpen F.affine.isCompact
  have hloc := fun y (_ : y ∈ π ⁻¹ᵁ W) =>
    exists_stalk_coordMul_eq_smul g q F.A F.n (-2) y
  have hv' : D.ellU₀.mulVec (v ∘ Sum.inl) + D.ellV₀.mulVec (v ∘ Sum.inr) = 0 := by
    rwa [← Matrix.fromCols_mulVec]
  rw [hU₀, hV₀] at hv'
  have hst0 := congrArg (enc ι F.data.b₀) hv'
  have hst1 := ((enc ι F.data.b₀).map_add _ _).symm.trans (hst0.trans (enc ι F.data.b₀).map_zero)
  have k1 := enc_mulVec ι F.data.b₁ F.data.b₀ Sum.inl
    (fun j => MMP.Chow.directImageSectionsMap π W (ψ' j)) (v ∘ Sum.inl)
  have k2 := enc_mulVec ι F.data.b₁ F.data.b₀ Sum.inr
    (fun j => MMP.Chow.directImageSectionsMap π W (ψ' j)) (v ∘ Sum.inr)
  have hst : coeffMapAdd Sum.inl (fun i => ((ψ' i).app (π ⁻¹ᵁ W)).hom)
        (enc ι F.data.b₁ (v ∘ Sum.inl)) +
      coeffMapAdd Sum.inr (fun i => ((ψ' i).app (π ⁻¹ᵁ W)).hom)
        (enc ι F.data.b₁ (v ∘ Sum.inr)) = 0 :=
    (congrArg₂ (· + ·) k1.symm k2.symm).trans hst1
  obtain ⟨w, hw1, hw2⟩ := coeff_glue ψ ψ' (π ⁻¹ᵁ W) hcomp hloc _ _ hst
  obtain ⟨w', rfl⟩ := enc_surjective ι F.data.b₂ w
  have e1 : -((∑ j, (MvPolynomial.X (Sum.inr j) : D.Pol) •
      ((LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π W (ψ j))).map
        ι.symm).map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol)).mulVec w') = v ∘ Sum.inl :=
    enc_injective ι F.data.b₁ (((enc ι F.data.b₁).map_neg _).trans
      ((congrArg Neg.neg (enc_mulVec ι F.data.b₂ F.data.b₁ Sum.inr
        (fun j => MMP.Chow.directImageSectionsMap π W (ψ j)) w')).trans hw1))
  have e2 : (∑ j, (MvPolynomial.X (Sum.inl j) : D.Pol) •
      ((LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π W (ψ j))).map
        ι.symm).map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol)).mulVec w' = v ∘ Sum.inr :=
    enc_injective ι F.data.b₁ ((enc_mulVec ι F.data.b₂ F.data.b₁ Sum.inl
        (fun j => MMP.Chow.directImageSectionsMap π W (ψ j)) w').trans hw2)
  refine ⟨w', ?_⟩
  set L₁v := ∑ j, (MvPolynomial.X (Sum.inr j) : D.Pol) •
      ((LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π W (ψ j))).map
        ι.symm).map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol)
  set L₁u := ∑ j, (MvPolynomial.X (Sum.inl j) : D.Pol) •
      ((LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π W (ψ j))).map
        ι.symm).map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol)
  funext x
  rcases x with i | i
  · show ((-D.ellV₁).mulVec w') i = v (Sum.inl i)
    rw [hV₁]
    exact (congrFun (Matrix.neg_mulVec w' L₁v) i).trans (congrFun e1 i)
  · show (D.ellU₁.mulVec w') i = v (Sum.inr i)
    rw [hU₁]
    exact congrFun e2 i

/-- For the local free data of a `KoszulFamily`, at a height-one prime `p` of `R[u, v]` lying over
the zero ideal of `R`, the localized complex is exact at `V₁ ⊕ V₁` and its cokernel `H₀` has
finite length. -/
theorem koszulFamily_horizontal {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d) {s : S} (F : KoszulFamily g π q d s) :
    let D := F.toLocalFreeData hS
    ∀ (p : Ideal D.Pol) [p.IsPrime], p.height = 1 →
      p.comap (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) = ⊥ →
        ExactAt D.A D.B p ∧ cokerLength D.B p ≠ ⊤ := by
  intro D p _ hp _
  refine ⟨exactAt_of_forall D.A D.B
    (koszulFamily_exact_middle sS sY hS hY g hg hgY π q hπq hdim d hd F) p, ?_⟩
  obtain ⟨x, hx⟩ := D.exists_isClosed_point
  obtain ⟨a, b, hab⟩ := exists_avoidsPair sS sY hS hY g hg hgY π q hπq hdim D.ι x hx
  obtain ⟨S₀, hS₀, -⟩ := isSplitExact_of_surjective_hom (K := FractionRing D.Pol)
    (D.evalPt x a b) (D.evalPt_surjective x hx a b)
    (koszulFamily_exact_of_avoid sS sY hS hY g hg hgY π q hπq hdim d hd F x hx a b hab)
  exact length_coker_ne_top_of_mul_eq_one D.B S₀ hS₀ p hp

variable {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)} {S 𝒞 : Scheme.{u}}
  {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}

/-- If every closed fibre admits an avoiding pair, the determinant `F` of the complex lies in
`R[u, v]`. -/
theorem complexDet_mem_polynomial (D : LocalFreeData g sS π q d s) (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b) :
    ∃ P : D.Pol, algebraMap D.Pol (FractionRing D.Pol) P = D.F := by
  haveI : IsIntegrallyClosed D.Pol :=
    isIntegrallyClosed_mvPolynomial_sum Γ(D.U, ⊤) (N + 1)
  exact MMP.Chow.exists_algebraMap_complexDet_eq (K := FractionRing D.Pol) (e := D.e)
    (A := D.A) (B := D.B) D.B_mul_A (fun p _ hp1 => by
      by_cases hq : p.comap (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) = ⊥
      · exact hD.horizontal p hp1 hq
      · -- vertical case: `p = q R[u, v]` for the nonzero prime `q = p ∩ R`
        haveI hqp : (p.comap (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol)).IsPrime :=
          Ideal.comap_isPrime _ _
        set q : Ideal Γ(D.U, ⊤) := p.comap (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol)
        have hqle : Ideal.map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) q ≤ p :=
          Ideal.map_le_iff_le_comap.2 le_rfl
        obtain ⟨𝔫, h𝔫, hq𝔫⟩ := Ideal.exists_le_maximal q hqp.ne_top
        obtain ⟨x, hxc, hker⟩ := exists_closed_pt_ker D.U 𝔫 h𝔫
        obtain ⟨a, b, hab⟩ := h0 x hxc
        have hpq : p = Ideal.map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) q := by
          haveI : (Ideal.map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) q).IsPrime := by
            have hk : Ideal.map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) q =
                RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk q) :
                  D.Pol →+* MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Γ(D.U, ⊤) ⧸ q)) := by
              rw [MvPolynomial.ker_map, Ideal.mk_ker]
            rw [hk]
            exact RingHom.ker_isPrime _
          refine (eq_of_le_of_not_lt hqle fun hlt => ?_).symm
          have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
          rw [hp1] at h1
          have h2 : (Ideal.map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) q).height = 0 := by
            have h' : (Ideal.map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) q).height + 1 ≤ 0 + 1 := by
              simpa using h1
            have := (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).1 h'
            exact le_antisymm this zero_le
          rw [Ideal.height_eq_zero_iff_eq_bot] at h2
          apply hq
          rw [eq_bot_iff]
          intro f hf
          have : (MvPolynomial.C f : D.Pol) ∈ Ideal.map (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) q :=
            Ideal.mem_map_of_mem _ hf
          rw [h2] at this
          exact Ideal.mem_bot.2 (MvPolynomial.C_eq_zero.1 (Ideal.mem_bot.1 this))
        have hsub : p ≤ RingHom.ker (D.evalPt x a b) := by
          rw [hpq, Ideal.map_le_iff_le_comap]
          intro f hf
          simp only [Ideal.mem_comap, RingHom.mem_ker]
          have : D.evalPt x a b (MvPolynomial.C f) = (D.U.Γevaluation x).hom f := by
            simp [LocalFreeData.evalPt]
          rw [this]
          exact hker f (hq𝔫 hf)
        exact exact_at_prime_of_residue (D.evalPt x a b) (D.evalPt_surjective x hxc a b) p hsub
          D.B_mul_A (hD.exact_of_avoid x hxc a b hab))

/-- If every closed fibre admits an avoiding pair, a polynomial `P` representing the determinant
is bihomogeneous of bidegree `(d, d)` in `(u, v)`. -/
theorem complexDet_isBihomogeneous (D : LocalFreeData g sS π q d s) (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b)
    (P : D.Pol) (hP : algebraMap D.Pol (FractionRing D.Pol) P = D.F) :
    ∀ e ∈ P.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d := by
  letI := MMP.Chow.structureAlgebra (k := k) (D.ι ≫ sS)
  haveI : Nontrivial Γ(D.U, ⊤) := D.isDomain.toNontrivial
  intro e he
  let two : Γ(D.U, ⊤)ˣ :=
    Units.map (algebraMap k Γ(D.U, ⊤)).toMonoidHom (Units.mk0 (2 : k) two_ne_zero)
  have htwo : (two : Γ(D.U, ⊤)) = algebraMap k Γ(D.U, ⊤) 2 := rfl
  have key : ∀ m n : ℕ, (two : Γ(D.U, ⊤)) ^ m = (two : Γ(D.U, ⊤)) ^ n → m = n := by
    intro m n h
    rw [htwo] at h
    exact two_pow_inj (K := k) (Γ := Γ(D.U, ⊤)) h
  constructor
  · have := D.scale_coeff_eq hD h0 two 1 P hP e he
    simp only [Units.val_one, one_pow, mul_one] at this
    exact key _ _ this
  · have := D.scale_coeff_eq hD h0 1 two P hP e he
    simp only [Units.val_one, one_pow, one_mul] at this
    exact key _ _ this

/-- The fibre complex over `κ(x)[u, v]` is generically split exact when an avoiding pair exists. -/
theorem fibre_isSplitExact (D : LocalFreeData g sS π q d s) (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b)
    (x : D.U) (hx : IsClosed ({x} : Set D.U)) :
    MMP.Chow.IsSplitExact D.e
      ((D.A.map (D.specHom x)).map (algebraMap (D.PolAt x) (FractionRing (D.PolAt x))))
      ((D.B.map (D.specHom x)).map (algebraMap (D.PolAt x) (FractionRing (D.PolAt x)))) := by
  obtain ⟨a, b, hab⟩ := h0 x hx
  let ev : D.PolAt x →+* D.U.residueField x := MvPolynomial.eval₂Hom (RingHom.id _)
    (Sum.elim (fun j => kEval (D.ι ≫ sS) x (a j)) (fun j => kEval (D.ι ≫ sS) x (b j)))
  have hev : ev.comp (D.specHom x) = D.evalPt x a b := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [ev, LocalFreeData.specHom, LocalFreeData.evalPt]
    · rcases i with i | i <;> simp [ev, LocalFreeData.specHom, LocalFreeData.evalPt]
  have hevs : Function.Surjective ev := fun y => ⟨MvPolynomial.C y, by simp [ev]⟩
  have hfib1 : MMP.Chow.IsSplitExact D.e ((D.A.map (D.specHom x)).map ev)
      ((D.B.map (D.specHom x)).map ev) := by
    simpa only [Matrix.map_map, ← RingHom.coe_comp, hev] using hD.exact_of_avoid x hx a b hab
  exact isSplitExact_of_surjective_hom (K := FractionRing (D.PolAt x)) ev hevs hfib1

/-- At a closed point `x`, the reduction of `P` to `κ(x)[u, v]` is the determinant of the fibre
complex at `x`. -/
theorem complexDet_specialize (D : LocalFreeData g sS π q d s) (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b)
    (P : D.Pol) (hP : algebraMap D.Pol (FractionRing D.Pol) P = D.F)
    (x : D.U) (hx : IsClosed ({x} : Set D.U)) :
    algebraMap (D.PolAt x) (FractionRing (D.PolAt x)) (D.specHom x P) = D.fibreDet x :=
  specialize_complexDet (K := FractionRing D.Pol) (K' := FractionRing (D.PolAt x))
    (D.specHom x) (MvPolynomial.map_surjective _ (Γevaluation_surjective (D.ι ≫ sS) x hx))
    (fibre_isSplitExact D hD h0 x hx) D.B_mul_A P hP

/-- If every closed fibre admits an avoiding pair, the coefficients of a polynomial `P`
representing the determinant generate the unit ideal of `R`. -/
theorem span_coeff_complexDet_eq_top (D : LocalFreeData g sS π q d s) (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b)
    (P : D.Pol) (hP : algebraMap D.Pol (FractionRing D.Pol) P = D.F) :
    Ideal.span (Set.range P.coeff) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, hx, hker⟩ := exists_closed_pt_ker D.U m hm
  have hz : D.specHom x P = 0 := by
    ext e
    simp only [LocalFreeData.specHom, MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    exact hker _ (hIm (Ideal.subset_span ⟨e, rfl⟩))
  have h5 := complexDet_specialize D hD h0 P hP x hx
  rw [hz, map_zero] at h5
  obtain ⟨S, hS, hdet⟩ := fibre_isSplitExact D hD h0 x hx
  have hBA : D.B.map (D.specHom x) * D.A.map (D.specHom x) = 0 := by
    rw [← Matrix.map_mul, D.B_mul_A]
    simp
  have hBA2 := MMP.Chow.map_mul_eq_zero (K := FractionRing (D.PolAt x)) hBA
  have hne0 : D.fibreDet x ≠ 0 := by
    change MMP.Chow.cayleyDet _ _ _ ≠ 0
    rw [MMP.Chow.cayleyDet_eq_inv_det hBA2 hS hdet]
    exact inv_ne_zero hdet
  exact hne0 h5.symm

/-! #### The Chow form of a closed fibre

For a closed point `t` of the base, write `X = π⁻¹(t)` for the fibre, `ψ : X ⟶ ℙᴺ` for its map to
projective space and `H = ψ^*𝒪(1)`. A hyperplane `a` is *regular* on `X` when the section
`ℓ_a = ∑ aⱼ xⱼ` of `H` is a nonzerodivisor on every stalk. The determinant `F` of the fibre complex
is a polynomial in `k[u, v]`; restricted to `u = a` it is, up to a scalar, the product over the
points `y` of the zero scheme of `ℓ_a` of the linear forms of `ψ(y)` with exponent the local length
of `𝒪_{X,y}/ℓ_a` (`koszulFamily_restrictU_eq`). Summing the local lengths over the points of a
curve `C ⊆ ψ(X)` gives `m_C · deg C` (`sum_fibreLen_eq`), the same sum for the incidence form of
`C` itself gives `deg C` (`sum_multiplicity_incForm_eq_degree`), and every prime factor of `F` is
an incidence form of a curve of `ψ(X)` (`fibrePoly_factor`); comparing exponents gives the
multiplicities. -/

section FibreChow

/-- Coordinates of a point of `ℙᴺ`: a nonzero vector at which its homogeneous ideal vanishes. -/
noncomputable def ptCoord (p : AlgebraicGeometry.Proj (polyGrading k N)) :
    Fin (N + 1) → k :=
  Classical.choose (exists_zero_of_prime (k := k) p)

/-- The linear form `∑ⱼ pⱼ vⱼ` of a point `p` of `ℙᴺ`; for a closed point it vanishes exactly on
the hyperplanes through `p`. -/
noncomputable def ptForm (p : AlgebraicGeometry.Proj (polyGrading k N)) :
    MvPolynomial (Fin (N + 1)) k :=
  ∑ j, MvPolynomial.C (ptCoord p j) * X j

/-- Evaluating `aeval g f` at `q` is evaluating `f` at the point `i ↦ eval q (g i)`. -/
theorem eval_aeval_eq {R σ : Type*} [CommSemiring R] (g : σ → MvPolynomial σ R) (q : σ → R)
    (f : MvPolynomial σ R) : eval q (aeval g f) = eval (fun i => eval q (g i)) f :=
  aeval_bind₁ q g f

/-- The coordinates `ptCoord p` are nonzero and every element of the homogeneous ideal of `p`
vanishes at them. -/
theorem ptCoord_spec (p : AlgebraicGeometry.Proj (polyGrading k N)) :
    ptCoord p ≠ 0 ∧ ∀ f ∈ p.asHomogeneousIdeal, eval (ptCoord p) f = 0 :=
  Classical.choose_spec (exists_zero_of_prime (k := k) p)

/-- The homogeneous ideal of a closed point of `ℙᴺ` is the ideal of the line of its coordinates. -/
theorem mem_closedPt_iff (p : AlgebraicGeometry.Proj (polyGrading k N))
    (hp : IsClosed ({p} : Set (AlgebraicGeometry.Proj (polyGrading k N))))
    (f : MvPolynomial (Fin (N + 1)) k) :
    f ∈ p.asHomogeneousIdeal ↔ f ∈ lineIdeal (ptCoord p) := by
  classical
  have hle : ∀ f, f ∈ p.asHomogeneousIdeal → f ∈ lineIdeal (ptCoord p) := by
    intro f hf
    rw [mem_lineIdeal_iff]
    intro m
    have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f m : _) :
        MvPolynomial (Fin (N + 1)) k) = homogeneousComponent m f :=
      MvPolynomial.decomposition.decompose'_apply f m
    exact (ptCoord_spec p).2 _ (e ▸ p.asHomogeneousIdeal.isHomogeneous m hf)
  refine ⟨hle f, fun hf => ?_⟩
  obtain ⟨p', hp'⟩ := exists_point_of_line (ptCoord p) (ptCoord_spec p).1
  have hp2 : IsClosed
      ({(p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))} :
        Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))) := hp
  have hpp' := (ProjectiveSpectrum.le_iff_mem_closure _ p p').mp fun g hg => (hp' g).2 (hle g hg)
  have hpp'' : p' = p := hp2.closure_subset hpp'
  rw [← hpp'']
  exact (hp' f).2 hf

/-- A hyperplane passes through a closed point exactly when its equation vanishes at the
coordinates of the point. -/
theorem linForm_mem_closedPt_iff (p : AlgebraicGeometry.Proj (polyGrading k N))
    (hp : IsClosed ({p} : Set (AlgebraicGeometry.Proj (polyGrading k N)))) (w : Fin (N + 1) → k) :
    linForm w ∈ p.asHomogeneousIdeal ↔ ∑ j, w j * ptCoord p j = 0 := by
  classical
  have hh : (linForm w).IsHomogeneous 1 := by
    refine IsHomogeneous.sum _ _ _ fun j _ => ?_
    simpa using (isHomogeneous_X k j).C_mul (w j)
  rw [mem_closedPt_iff p hp, mem_lineIdeal_iff]
  constructor
  · intro h
    have := h 1
    rw [homogeneousComponent_of_mem hh, if_pos rfl] at this
    simpa [linForm] using this
  · intro h m
    rw [homogeneousComponent_of_mem hh]
    split_ifs with hm
    · simpa [linForm] using h
    · simp

/-- The coefficient of `vⱼ` in `ptForm p` is the `j`-th coordinate of `p`. -/
theorem coeff_ptForm (p : AlgebraicGeometry.Proj (polyGrading k N)) (j : Fin (N + 1)) :
    (ptForm p).coeff (Finsupp.single j 1) = ptCoord p j := by
  classical
  simp only [ptForm, coeff_sum, coeff_C_mul, coeff_X', Finsupp.single_eq_single_iff]
  rw [Finset.sum_eq_single j]
  · simp
  · exact fun b _ hb => by simp [Ne.symm hb, hb]
  · simp

/-- The linear form `ptForm p` has total degree one. -/
theorem totalDegree_ptForm (p : AlgebraicGeometry.Proj (polyGrading k N)) :
    (ptForm p).totalDegree = 1 := by
  classical
  apply le_antisymm
  · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact (totalDegree_mul _ _).trans (by simp)
  · obtain ⟨j, hj⟩ : ∃ j, ptCoord p j ≠ 0 := Function.ne_iff.mp (ptCoord_spec p).1
    have := le_totalDegree (s := Finsupp.single j 1) (p := ptForm p)
      (by rwa [mem_support_iff, coeff_ptForm])
    simpa using this

/-- A polynomial of total degree one over a field is irreducible. -/
theorem irreducible_of_totalDegree_eq_one {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} (hf : f.totalDegree = 1) : Irreducible f := by
  refine MvPolynomial.irreducible_of_totalDegree_eq_one hf fun x hx => ?_
  obtain ⟨i, hi⟩ : ∃ i, f.coeff i ≠ 0 := by
    by_contra h
    push Not at h
    have : f = 0 := MvPolynomial.ext _ _ fun i => by simpa using h i
    simp [this] at hf
  exact isUnit_iff_ne_zero.2 fun h0 => hi (by simpa [h0] using hx i)

/-- Restriction of a polynomial in the pair `(u, v)` to `u = a`. -/
noncomputable def restrictU (a : Fin (N + 1) → k) :
    MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k →ₐ[k] MvPolynomial (Fin (N + 1)) k :=
  aeval (Sum.elim (fun j => MvPolynomial.C (a j)) X)

/-- The hyperplane bundle on the fibre over `t`. -/
noncomputable abbrev fibreH (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) : (π.fiber t).Modules :=
  (Scheme.Modules.pullback (π.fiberι t)).obj (hyperplaneBundle g q)

/-- The section `ℓ_a` on the fibre over `t`. -/
noncomputable def fibreLin (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (a : Fin (N + 1) → k) :
    Γ(fibreH g π q t, ⊤) :=
  (pullbackGlobalSections (π.fiberι t) (hyperplaneBundle g q)).hom (linSection g q a)

/-- The restriction `fibreH g π q t` of the hyperplane bundle to the fibre over `t` is
invertible. -/
theorem isInvertibleModule_fibreH (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) :
    Stacks.Ample.IsInvertibleModule (π.fiber t) (fibreH g π q t) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback (π.fiberι t) (hyperplaneBundle g q)

attribute [local instance] isInvertibleModule_fibreH

/-- The `j`-th coordinate section `x_j` on the fibre over `t`. -/
noncomputable def fibreCoord (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (j : Fin (N + 1)) :
    Γ(fibreH g π q t, ⊤) :=
  (pullbackGlobalSections (π.fiberι t) (hyperplaneBundle g q)).hom (coordSection g q j)

/-- A pulled back degree-one section does not vanish at a point of the fibre exactly when its
linear form does not lie in the image point. -/
theorem mem_nonvanishingLocus_fibre_iff (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S)
    (f : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1) (y : π.fiber t) :
    y ∈ Stacks.Ample.nonvanishingLocus (fibreH g π q t)
      ((pullbackGlobalSections (π.fiberι t) (hyperplaneBundle g q)).hom
        ((pullbackGlobalSections (q ≫ g)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)).hom
          (ProjectiveSpectrum.Proj.degreeSection (polyGrading k N) 1 f))) ↔
      (f : MvPolynomial (Fin (N + 1)) k) ∉ (fibrePsi g π q t y).asHomogeneousIdeal := by
  rw [← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections,
    Set.mem_preimage]
  erw [← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections (q ≫ g)]
  rw [Set.mem_preimage]
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (N + 1)) k
  exact Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) 1 1 f (x := (q ≫ g) (π.fiberι t y)) (by
      rw [Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.whereInvertible_eq_top _ hgen one_pos]
      trivial)

/-- The section `ℓ_a` on the fibre does not vanish at `y` if and only if the linear form
`linForm a` is not in the homogeneous ideal of the image of `y` in `ℙᴺ`. -/
theorem mem_nonvanishingLocus_fibreLin_iff
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S)
    (q : 𝒞 ⟶ Y) (t : S) (a : Fin (N + 1) → k) (y : π.fiber t) :
    y ∈ Stacks.Ample.nonvanishingLocus (fibreH g π q t) (fibreLin g π q t a) ↔
      linForm a ∉ (fibrePsi g π q t y).asHomogeneousIdeal := by
  rw [fibreLin, linSection_eq]
  exact mem_nonvanishingLocus_fibre_iff g π q t ⟨_, linForm_mem a⟩ y

/-- The coordinate section `x_j` on the fibre does not vanish at `y` if and only if `X j` is not in
the homogeneous ideal of the image of `y` in `ℙᴺ`. -/
theorem mem_nonvanishingLocus_fibreCoord_iff
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S)
    (q : 𝒞 ⟶ Y) (t : S) (j : Fin (N + 1)) (y : π.fiber t) :
    y ∈ Stacks.Ample.nonvanishingLocus (fibreH g π q t) (fibreCoord g π q t j) ↔
      (X j : MvPolynomial (Fin (N + 1)) k) ∉ (fibrePsi g π q t y).asHomogeneousIdeal :=
  mem_nonvanishingLocus_fibre_iff g π q t
    ⟨X j, (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X k j)⟩ y

/-- At every point of the fibre some coordinate section `x_j` does not vanish. -/
theorem exists_mem_nonvanishingLocus_fibreCoord
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S)
    (q : 𝒞 ⟶ Y) (t : S) (y : π.fiber t) :
    ∃ j, y ∈ Stacks.Ample.nonvanishingLocus (fibreH g π q t) (fibreCoord g π q t j) := by
  haveI : (fibrePsi g π q t y).asHomogeneousIdeal.toIdeal.IsPrime := (fibrePsi g π q t y).isPrime
  obtain ⟨j, hj⟩ := exists_notMem_X (k := k) (N := N)
    (𝔭 := (fibrePsi g π q t y).asHomogeneousIdeal.toIdeal)
    (fun hle => (fibrePsi g π q t y).not_irrelevant_le hle)
  exact ⟨j, (mem_nonvanishingLocus_fibreCoord_iff g π q t j y).2 hj⟩

/-- A coordinate not vanishing at the point. -/
noncomputable def fibreIdx (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (y : π.fiber t) : Fin (N + 1) :=
  (exists_mem_nonvanishingLocus_fibreCoord g π q t y).choose

/-- The coordinate section indexed by `fibreIdx g π q t y` does not vanish at `y`. -/
theorem fibreIdx_mem (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (y : π.fiber t) :
    y ∈ Stacks.Ample.nonvanishingLocus (fibreH g π q t) (fibreCoord g π q t (fibreIdx g π q t y)) :=
  (exists_mem_nonvanishingLocus_fibreCoord g π q t y).choose_spec

/-- The local equation of `ℓ_a` at `y`: its coordinate relative to a coordinate section not
vanishing at `y`. -/
noncomputable def fibreEq (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (a : Fin (N + 1) → k)
    (y : π.fiber t) : (π.fiber t).presheaf.stalk y :=
  (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus (fibreH g π q t) _
    (fibreIdx_mem g π q t y)).coord (((fibreH g π q t).presheaf.Γgerm y).hom (fibreLin g π q t a))

/-- The local length of the zero scheme of `ℓ_a` at a point `y` of the fibre. -/
noncomputable def fibreLen (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (a : Fin (N + 1) → k)
    (y : π.fiber t) : ℕ :=
  (Module.length ((π.fiber t).presheaf.stalk y)
    ((π.fiber t).presheaf.stalk y ⧸ Ideal.span {fibreEq g π q t a y})).toNat

/-- The hyperplane `a` is regular on the fibre over `t`: it contains the image of no associated
point of the fibre. -/
def FibreRegular (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (a : Fin (N + 1) → k) : Prop :=
  ∀ ζ ∈ Stacks.Divisors.schemeAssociatedPoints (π.fiber t),
    linForm a ∉ (fibrePsi g π q t ζ).asHomogeneousIdeal

/-- If the hyperplane `a` is regular on the fibre over `t`, then `ℓ_a` does not vanish at any
associated point of the fibre. -/
theorem FibreRegular.mem_nonvanishingLocus {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {S 𝒞 : Scheme.{u}} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {t : S} {a : Fin (N + 1) → k}
    (h : FibreRegular g π q t a) :
    ∀ ζ ∈ Stacks.Divisors.schemeAssociatedPoints (π.fiber t),
      ζ ∈ Stacks.Ample.nonvanishingLocus (fibreH g π q t) (fibreLin g π q t a) :=
  fun ζ hζ => (mem_nonvanishingLocus_fibreLin_iff g π q t a ζ).2 (h ζ hζ)

/-- The local equation of `ℓ_a` at `y` is a unit if and only if the linear form `linForm a` is not
in the homogeneous ideal of the image of `y` in `ℙᴺ`. -/
theorem isUnit_fibreEq_iff (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (a : Fin (N + 1) → k) (y : π.fiber t) :
    IsUnit (fibreEq g π q t a y) ↔ linForm a ∉ (fibrePsi g π q t y).asHomogeneousIdeal :=
  (isUnit_coord_iff _ _ _ (fibreIdx_mem g π q t y)).trans
    (mem_nonvanishingLocus_fibreLin_iff g π q t a y)

/-- The hyperplane `a` separates the curve `C` on the fibre over `t`: every irreducible component
of the fibre through a point of `ψ⁻¹(C ∩ H_a)` maps onto `C`. -/
def FibreSeparates (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) (a : Fin (N + 1) → k)
    (C : Mori.ProperCurve (projToSpecCoeff k N)) : Prop :=
  ∀ y ξ : π.fiber t, fibrePsi g π q t y ∈ closure ({C.point} : Set _) →
    linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal → ξ ⤳ y →
    closure ({ξ} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t) →
    fibrePsi g π q t ξ = C.point

/-- `F'` is a fibre polynomial at `x`: its image in `κ(x)[u, v]` is the reduction of a polynomial
representing the determinant of the Koszul complex. -/
def IsFibrePoly {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)} {S 𝒞 : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
    (D : LocalFreeData g sS π q d s) (x : D.U)
    (F' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) : Prop :=
  ∃ P : D.Pol, algebraMap D.Pol (FractionRing D.Pol) P = D.F ∧
    MvPolynomial.map (kEval (D.ι ≫ sS) x) F' = D.specHom x P

/-- The degree of `𝒪(1)` on a curve of `ℙᴺ`. -/
noncomputable def curveDeg (C : Mori.ProperCurve (projToSpecCoeff k N)) : ℤ :=
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  C.degree k (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)

/-- **A pair avoiding the fibre does not lie on the fibre polynomial.** -/
theorem fibrePoly_eval_ne_zero {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
    (D : LocalFreeData g sS π q d s) (hD : D.Realizes) (x : D.U) (hx : IsClosed ({x} : Set D.U))
    {F' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k} (hF' : IsFibrePoly D x F')
    (a b : Fin (N + 1) → k) (hab : AvoidsPair (fibreImage g π q D.ι x) a b) :
    eval (Sum.elim a b) F' ≠ 0 := by
  classical
  obtain ⟨P, hP, hPF⟩ := hF'
  set ψ := D.evalPt x a b
  have hfib := hD.exact_of_avoid x hx a b hab
  have hid : ∀ {m n : Type} (M : Matrix m n (D.U.residueField x)),
      M.map (algebraMap (D.U.residueField x) (D.U.residueField x)) = M := fun _ => rfl
  have key := specialize_complexDet (K := FractionRing D.Pol) (K' := D.U.residueField x) ψ
    (D.evalPt_surjective x hx a b) (by rwa [hid, hid]) D.B_mul_A P hP
  have hBA : D.B.map ψ * D.A.map ψ = 0 := by
    rw [← Matrix.map_mul, D.B_mul_A]
    simp
  have hne : MMP.Chow.complexDet (D.U.residueField x) D.e (D.A.map ψ) (D.B.map ψ) ≠ 0 := by
    obtain ⟨S, hS, hd⟩ := hfib
    rw [MMP.Chow.complexDet, hid, hid, MMP.Chow.cayleyDet_eq_inv_det hBA hS hd]
    exact inv_ne_zero hd
  have hψP : ψ P = kEval (D.ι ≫ sS) x (eval (Sum.elim a b) F') := by
    have h1 : ψ P = eval (Sum.elim (fun j => kEval (D.ι ≫ sS) x (a j))
        (fun j => kEval (D.ι ≫ sS) x (b j))) (D.specHom x P) := by
      rw [LocalFreeData.specHom, MvPolynomial.eval_map]
      rfl
    rw [h1, ← hPF, MvPolynomial.eval_map]
    have h2 := MvPolynomial.eval₂_comp_left (kEval (D.ι ≫ sS) x) (RingHom.id k) (Sum.elim a b) F'
    refine Eq.trans ?_ h2.symm
    congr 1
    funext i
    rcases i with i | i <;> rfl
  intro h0
  apply hne
  rw [← key, hψP, h0, map_zero, map_zero]

/-- The proper curves of `ℙᴺ` whose generic points lie in the image of the fibre over `t`. -/
def fibreCurves (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) {S 𝒞 : Scheme.{u}}
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) : Set (Mori.ProperCurve (projToSpecCoeff k N)) :=
  {C | C.point ∈ Set.range (fibrePsi g π q t)}

/-- The incidence form chosen for a proper curve of `ℙᴺ`. -/
noncomputable def incForm0 (C : Mori.ProperCurve (projToSpecCoeff k N)) :
    MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k :=
  Classical.choose (exists_incForm C)

/-- The chosen form `incForm0 C` is an incidence form of `C`. -/
theorem incForm_incForm0 (C : Mori.ProperCurve (projToSpecCoeff k N)) :
    IncForm C (incForm0 C) :=
  Classical.choose_spec (exists_incForm C)

/-- The generic point of a proper curve is not a closed point. -/
theorem exists_specializes_ne_of_isProperCurve {G : Scheme.{u}} (sG : G ⟶ Spec (.of k))
    (p : G) (h : Mori.IsProperCurve sG p) : ∃ w, p ⤳ w ∧ w ≠ p := by
  by_contra hcon
  push Not at hcon
  have hsub : Subsingleton (closure ({p} : Set G)) := by
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext ((hcon a (specializes_iff_mem_closure.mpr ha)).trans
      (hcon b (specializes_iff_mem_closure.mpr hb)).symm)
  have h1 := h.dim_eq
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq] at h1
  have h2 := @topologicalKrullDim_zero_of_discreteTopology (closure ({p} : Set G)) _
    (@Subsingleton.discreteTopology _ _ hsub)
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- Every curve of the image of a closed fibre is the image of the generic point of a component of
the fibre. -/
theorem exists_fibreComponent_of_mem_fibreCurves {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (t : S) (ht : IsClosed ({t} : Set S)) (C : Mori.ProperCurve (projToSpecCoeff k N))
    (hC : C ∈ fibreCurves g π q t) :
    ∃ ξ ∈ fibreComponents π t, fibrePsi g π q t ξ = C.point := by
  obtain ⟨hψp, -, hdimF, -, hcover, -⟩ :=
    fibre_facts sS sY hS hY g hg hgY π q hπq hdim t ht
  haveI := hψp
  obtain ⟨y, hy⟩ := hC
  obtain ⟨ξ, hξ, hξy⟩ := hcover y
  refine ⟨y, ?_, hy⟩
  by_cases hξeq : ξ = y
  · exact hξeq ▸ hξ
  exfalso
  obtain ⟨w, hw, hwne⟩ :=
    exists_specializes_ne_of_isProperCurve (projToSpecCoeff k N) C.point C.isProperCurve
  rw [← hy] at hw hwne
  obtain ⟨z, hyz, rfl⟩ := exists_specializes_lift (fibrePsi g π q t).isClosedMap hw
  exact not_chain_of_topologicalKrullDim_le_one hdimF hξy hyz hξeq (fun h => hwne (by rw [h]))

/-- The curves of the image of a closed fibre are finitely many. -/
theorem finite_fibreCurves {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (t : S) (ht : IsClosed ({t} : Set S)) : (fibreCurves g π q t).Finite := by
  obtain ⟨-, -, -, hfin, -, -⟩ := fibre_facts sS sY hS hY g hg hgY π q hπq hdim t ht
  have hsub : fibreCurves g π q t ⊆ (fun C : Mori.ProperCurve (projToSpecCoeff k N) => C.point) ⁻¹'
      (fibrePsi g π q t '' fibreComponents π t) := fun C hC =>
    exists_fibreComponent_of_mem_fibreCurves sS sY hS hY g hg hgY π q hπq hdim t ht C hC
  exact (Set.Finite.preimage (fun a _ b _ hab => Mori.ProperCurve.ext hab)
    (hfin.image _)).subset hsub

/-- A finite sum of finitely supported functions vanishes at `a` when each summand does. -/
theorem finsum_apply_eq_zero {ι α M : Type*} [AddCommMonoid M] (f : ι → α →₀ M) (a : α)
    (h : ∀ i, f i a = 0) : (∑ᶠ i, f i) a = 0 := by
  classical
  by_cases hfs : (Function.support f).Finite
  · rw [finsum_eq_sum f hfs, Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun i _ => h i
  · rw [finsum_of_infinite_support hfs]
    rfl

/-- A curve with a nonzero coefficient in the cycle of a fibre lies in its image. -/
theorem mem_fibreCurves_of_cyc_ne_zero {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S)
    (C : Mori.ProperCurve (projToSpecCoeff k N)) (hC : cyc g sS π q t C ≠ 0) :
    C ∈ fibreCurves g π q t := by
  classical
  by_contra hnot
  apply hC
  unfold cyc
  refine finsum_apply_eq_zero _ C fun C' => ?_
  rw [Finsupp.smul_apply]
  unfold Mori.cyclePushforwardOfPoint
  split_ifs with h
  · rw [Finsupp.single_apply, if_neg, smul_zero]
    intro heq
    apply hnot
    exact ⟨C'.1.point, by rw [← heq]⟩
  · simp

/-- The two linear forms `∑ qⱼ uⱼ` and `∑ qⱼ vⱼ` of a nonzero vector have no common irreducible
factor. -/
theorem not_dvd_sum_C_mul_X_inl_and_inr (q : Fin (N + 1) → k) (hq : q ≠ 0)
    (H : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) (hH : Irreducible H) :
    ¬ (H ∣ ∑ j, MvPolynomial.C (q j) * X (Sum.inl j) ∧
      H ∣ ∑ j, MvPolynomial.C (q j) * X (Sum.inr j)) := by
  classical
  rintro ⟨h1, h2⟩
  obtain ⟨j0, hj0⟩ : ∃ j, q j ≠ 0 := Function.ne_iff.mp hq
  have hdeg : (∑ j, MvPolynomial.C (q j) * X (Sum.inl j) :
      MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k).totalDegree = 1 := by
    apply le_antisymm
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
      exact (totalDegree_mul _ _).trans (by simp)
    · have hc : (∑ j, MvPolynomial.C (q j) * X (Sum.inl j) :
          MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k).coeff (Finsupp.single (Sum.inl j0) 1) =
          q j0 := by
        simp only [coeff_sum, coeff_C_mul, coeff_X', Finsupp.single_eq_single_iff]
        rw [Finset.sum_eq_single j0]
        · simp
        · exact fun b _ hb => by simp [Ne.symm hb, hb]
        · simp
      have := le_totalDegree (s := Finsupp.single (Sum.inl j0) 1)
        (p := (∑ j, MvPolynomial.C (q j) * X (Sum.inl j) :
          MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)) (by rwa [mem_support_iff, hc])
      simpa using this
  have hass := hH.associated_of_dvd (irreducible_of_totalDegree_eq_one hdeg) h1
  obtain ⟨m, hm⟩ := hass.dvd_iff_dvd_left.1 h2
  let w : Fin (N + 1) ⊕ Fin (N + 1) → k := Sum.elim 0 (Pi.single j0 1)
  have := congrArg (eval w) hm
  simp only [map_sum, map_mul, eval_C, eval_X, w, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_mul, Pi.single_apply, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact hj0 this

/-- **The fibre polynomial is a product of incidence forms of the curves of the image.** -/
theorem fibrePoly_factor {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d) {s : S} (F : KoszulFamily g π q d s)
    (x : (F.toLocalFreeData hS).U) (hx : IsClosed ({x} : Set (F.toLocalFreeData hS).U))
    {F' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    (hF' : IsFibrePoly (F.toLocalFreeData hS) x F')
    (T : Finset (Mori.ProperCurve (projToSpecCoeff k N)))
    (hT : (T : Set _) = fibreCurves g π q ((F.toLocalFreeData hS).ι x)) :
    ∃ (c : k) (e : Mori.ProperCurve (projToSpecCoeff k N) → ℕ), c ≠ 0 ∧
      F' = MvPolynomial.C c * ∏ C ∈ T, incForm0 C ^ e C := by
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set t := (F.toLocalFreeData hS).ι x
  have ht : IsClosed ({t} : Set S) :=
    isClosed_image_of_isClosed sS ((F.toLocalFreeData hS).ι ≫ sS) (F.toLocalFreeData hS).ι rfl x hx
  have hD : (F.toLocalFreeData hS).Realizes :=
    ⟨koszulFamily_exact_of_avoid sS sY hS hY g hg hgY π q hπq hdim d hd F,
      koszulFamily_horizontal sS sY hS hY g hg hgY π q hπq hdim d hd F⟩
  obtain ⟨-, -, -, hfinΞ, hcover, hclass⟩ := fibre_facts sS sY hS hY g hg hgY π q hπq hdim t ht
  set ψ := fibrePsi g π q t
  have hne : ∀ u v : Fin (N + 1) → k, eval (Sum.elim u v) F' = 0 →
      ∃ y, linForm u ∈ (ψ y).asHomogeneousIdeal ∧ linForm v ∈ (ψ y).asHomogeneousIdeal := by
    intro u v h
    by_contra hcon
    push Not at hcon
    refine fibrePoly_eval_ne_zero (F.toLocalFreeData hS) hD x hx hF' u v ?_ h
    rw [fibreImage_eq_range sS g π q _ x hx]
    rintro p ⟨y, rfl⟩ ⟨h1, h2⟩
    exact hcon y h1 h2
  obtain ⟨a, b, hab⟩ :=
    exists_avoidsPair sS sY hS hY g hg hgY π q hπq hdim (F.toLocalFreeData hS).ι x hx
  have hF'0 : F' ≠ 0 := by
    rintro rfl
    exact fibrePoly_eval_ne_zero (F.toLocalFreeData hS) hD x hx hF' a b hab (map_zero _)
  let tset : Finset (π.fiber t) := hfinΞ.toFinset.filter fun ξ => IsClosed ({ψ ξ} : Set _)
  have hZ : ∀ w : Fin (N + 1) ⊕ Fin (N + 1) → k, eval w F' = 0 →
      (∃ C ∈ T, eval w (incForm0 C) = 0) ∨ ∃ ξ ∈ tset,
        eval w (∑ j, MvPolynomial.C (ptCoord (ψ ξ) j) * X (Sum.inl j)) = 0 ∧
        eval w (∑ j, MvPolynomial.C (ptCoord (ψ ξ) j) * X (Sum.inr j)) = 0 := by
    intro w hw
    have hwe : Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := Sum.elim_comp_inl_inr w
    rw [← hwe] at hw
    obtain ⟨y, hu, hv⟩ := hne _ _ hw
    obtain ⟨ξ, hξ, hξy⟩ := hcover y
    rcases hclass ξ hξ with hcl | hcurve
    · right
      have hyξ : ψ y = ψ ξ := hcl.closure_subset
        (specializes_iff_mem_closure.mp (hξy.map (fibrePsi g π q t).continuous))
      refine ⟨ξ, Finset.mem_filter.2 ⟨hfinΞ.mem_toFinset.2 hξ, hcl⟩, ?_, ?_⟩
      · rw [hyξ, linForm_mem_closedPt_iff _ hcl] at hu
        rw [← hwe, ← hu]
        simp only [map_sum, map_mul, eval_C, eval_X, Sum.elim_inl, Sum.elim_inr,
          Function.comp_apply]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      · rw [hyξ, linForm_mem_closedPt_iff _ hcl] at hv
        rw [← hwe, ← hv]
        simp only [map_sum, map_mul, eval_C, eval_X, Sum.elim_inl, Sum.elim_inr,
          Function.comp_apply]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · left
      let C : Mori.ProperCurve (projToSpecCoeff k N) := ⟨ψ ξ, hcurve⟩
      have hCT : C ∈ T := by
        rw [← Finset.mem_coe, hT]
        exact ⟨ξ, rfl⟩
      refine ⟨C, hCT, ?_⟩
      rw [← hwe, (incForm_incForm0 C).2]
      exact ⟨ψ y, specializes_iff_mem_closure.mp (hξy.map (fibrePsi g π q t).continuous), hu, hv⟩
  exact exists_eq_C_mul_prod_pow_of_zeroLocus_subset T incForm0
    (fun C _ => (incForm_incForm0 C).1) tset
    (fun ξ => ∑ j, MvPolynomial.C (ptCoord (ψ ξ) j) * X (Sum.inl j))
    (fun ξ => ∑ j, MvPolynomial.C (ptCoord (ψ ξ) j) * X (Sum.inr j))
    (fun ξ _ H hH => not_dvd_sum_C_mul_X_inl_and_inr _ (ptCoord_spec _).1 H hH) F' hF'0 hZ

/-- **A hyperplane avoiding finitely many points of `ℙᴺ`.** -/
theorem exists_linForm_notMem (B : Set (AlgebraicGeometry.Proj (polyGrading k N)))
    (hB : B.Finite) : ∃ a : Fin (N + 1) → k, ∀ p ∈ B, linForm a ∉ p.asHomogeneousIdeal := by
  classical
  choose P hP0 hP using exists_poly_of_point (k := k) (N := N)
  obtain ⟨a, ha⟩ : ∃ a, eval a (∏ p ∈ hB.toFinset, P p) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact (Finset.prod_ne_zero_iff.2 fun p _ => hP0 p)
      (MvPolynomial.funext fun w => by simpa using hcon w)
  refine ⟨a, fun p hp hmem => ?_⟩
  rw [map_prod] at ha
  exact (Finset.prod_ne_zero_iff.mp ha) p (hB.mem_toFinset.2 hp) (hP p a hmem)

/-- Projective space `ℙᴺ_k` is a Noetherian scheme. -/
theorem isNoetherian_proj : AlgebraicGeometry.IsNoetherian
    (AlgebraicGeometry.Proj (polyGrading k N)) := by
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N
  exact Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k
    (projToSpecCoeff k N)

attribute [local instance] isNoetherian_proj

/-- The closure of the generic point of a proper curve of `ℙᴺ` has dimension one. -/
theorem topologicalKrullDim_closure_properCurve (C : Mori.ProperCurve (projToSpecCoeff k N)) :
    topologicalKrullDim
      (closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N)))) ≤ 1 :=
  ((MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq C.point).symm.trans C.dim_eq).le

/-- No three distinct points of a proper curve form a chain of specializations. -/
theorem not_chain_closure_properCurve (C : Mori.ProperCurve (projToSpecCoeff k N))
    {a b c : AlgebraicGeometry.Proj (polyGrading k N)} (ha : a ∈ closure ({C.point} : Set _))
    (hb : b ∈ closure ({C.point} : Set _)) (hc : c ∈ closure ({C.point} : Set _))
    (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b) (hbc' : b ≠ c) : False := by
  refine not_chain_of_topologicalKrullDim_le_one (topologicalKrullDim_closure_properCurve C)
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (c := ⟨c, hc⟩) ?_ ?_ (fun h => hab' (congrArg Subtype.val h))
    (fun h => hbc' (congrArg Subtype.val h))
  · exact (subtype_specializes_iff _ _).2 hab
  · exact (subtype_specializes_iff _ _).2 hbc

/-- If the generic point of a curve lies on another curve, the two curves are equal. -/
theorem eq_of_point_mem_closure (C C' : Mori.ProperCurve (projToSpecCoeff k N))
    (h : C.point ∈ closure ({C'.point} : Set _)) : C = C' := by
  by_contra hne
  have hne' : C'.point ≠ C.point := fun h' => hne (Mori.ProperCurve.ext h'.symm)
  obtain ⟨w, hw, hwne⟩ :=
    exists_specializes_ne_of_isProperCurve (projToSpecCoeff k N) C.point C.isProperCurve
  have hsp : C'.point ⤳ C.point := specializes_iff_mem_closure.mpr h
  exact not_chain_closure_properCurve C' (subset_closure rfl) h
    (specializes_iff_mem_closure.mp (hsp.trans hw)) hsp hw hne' hwne.symm

/-- **Two distinct curves of `ℙᴺ` meet in finitely many closed points.** -/
theorem finite_inter_of_ne (C C' : Mori.ProperCurve (projToSpecCoeff k N)) (hne : C ≠ C') :
    {p | p ∈ closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))) ∧
        p ∈ closure ({C'.point} : Set (AlgebraicGeometry.Proj (polyGrading k N)))}.Finite ∧
      ∀ p, p ∈ closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))) →
        p ∈ closure ({C'.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))) →
        IsClosed ({p} : Set (AlgebraicGeometry.Proj (polyGrading k N))) := by
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N
  haveI : CompactSpace (AlgebraicGeometry.Proj (polyGrading k N)) :=
    QuasiCompact.compactSpace_of_compactSpace (projToSpecCoeff k N)
  have hcl : ∀ p, p ∈ closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))) →
      p ∈ closure ({C'.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))) →
      IsClosed ({p} : Set (AlgebraicGeometry.Proj (polyGrading k N))) := by
    intro p hp hp'
    by_contra hpc
    have hpC : p ≠ C.point := by
      rintro rfl
      exact hne (eq_of_point_mem_closure C C' hp')
    obtain ⟨w, hw, hwc⟩ := (isClosed_closure (s := ({p} : Set (AlgebraicGeometry.Proj
      (polyGrading k N))))).exists_closed_singleton ⟨p, subset_closure rfl⟩
    have hwp : w ≠ p := fun h => hpc (h ▸ hwc)
    have hsp : C.point ⤳ p := specializes_iff_mem_closure.mpr hp
    have hpw : p ⤳ w := specializes_iff_mem_closure.mpr hw
    exact not_chain_closure_properCurve C (subset_closure rfl) hp
      (specializes_iff_mem_closure.mp (hsp.trans hpw)) hsp hpw hpC.symm hwp.symm
  refine ⟨finite_of_isClosed_of_forall_isClosed (isClosed_closure.inter isClosed_closure)
    fun p hp => hcl p hp.1 hp.2, hcl⟩

/-- **The zero scheme of a regular hyperplane on the fibre** consists of finitely many closed
points, mapping to closed points, and the local lengths are positive exactly there. -/
theorem fibreZero_facts {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (t : S) (ht : IsClosed ({t} : Set S)) (a : Fin (N + 1) → k) (hreg : FibreRegular g π q t a) :
    {y | linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal}.Finite ∧
      (∀ y, linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal →
        IsClosed ({fibrePsi g π q t y} : Set _)) ∧
      ∀ y, fibreLen g π q t a y ≠ 0 ↔ linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal := by
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  obtain ⟨hψp, hFprop, hdimF, -, -, -⟩ := fibre_facts sS sY hS hY g hg hgY π q hπq hdim t ht
  haveI := hFprop
  haveI : LocallyOfFiniteType (π.fiberι t ≫ π ≫ sS) := hFprop.toLocallyOfFiniteType
  haveI : QuasiCompact (π.fiberι t ≫ π ≫ sS) :=
    @instQuasiCompactOfUniversallyClosed _ _ _ hFprop.toUniversallyClosed
  haveI : IsLocallyNoetherian (π.fiber t) :=
    LocallyOfFiniteType.isLocallyNoetherian (π.fiberι t ≫ π ≫ sS)
  haveI : CompactSpace (π.fiber t) :=
    QuasiCompact.compactSpace_of_compactSpace (π.fiberι t ≫ π ≫ sS)
  haveI : AlgebraicGeometry.IsNoetherian (π.fiber t) := AlgebraicGeometry.IsNoetherian.mk
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N
  have hφs : fibrePsi g π q t ≫ projToSpecCoeff k N = π.fiberι t ≫ π ≫ sS := by
    rw [Category.assoc, Category.assoc, hgY, ← hπq]
  set Z := {y | linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal} with hZdef
  have hZ : Z = (Stacks.Ample.nonvanishingLocus (fibreH g π q t) (fibreLin g π q t a))ᶜ := by
    ext y
    simp only [hZdef, Set.mem_setOf_eq, Set.mem_compl_iff, mem_nonvanishingLocus_fibreLin_iff,
      not_not]
  have hZc : IsClosed Z := by
    rw [hZ]
    exact (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus _ _ _).isClosed_compl
  obtain ⟨hfin, hcl⟩ := finite_isClosed_of_disjoint_assoc hdimF hZc fun z hz hza => hreg z hza hz
  refine ⟨hfin, fun y hy => ?_, fun y => ?_⟩
  · exact isClosed_image_of_isClosed (projToSpecCoeff k N) (π.fiberι t ≫ π ≫ sS)
      (fibrePsi g π q t) hφs y (hcl y hy)
  · have hc := coord_mem_nonZeroDivisors (fibreH g π q t) (fibreLin g π q t a)
      (fibreCoord g π q t (fibreIdx g π q t y)) hreg.mem_nonvanishingLocus (fibreIdx_mem g π q t y)
    have hfin' := length_quotient_span_ne_top hdimF y hc
    unfold fibreLen
    rw [Ne, ENat.toNat_eq_zero, not_or, length_quotient_span_eq_zero_iff]
    have := isUnit_fibreEq_iff g π q t a y
    unfold fibreEq at this ⊢
    tauto

/-- **A good hyperplane.** There is a hyperplane `a` regular on the fibre, separating every curve
of the image, containing none of them, and meeting the image of the fibre only on these curves. -/
theorem exists_goodHyperplane {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (t : S) (ht : IsClosed ({t} : Set S)) :
    ∃ a : Fin (N + 1) → k, FibreRegular g π q t a ∧
      (∀ C ∈ fibreCurves g π q t, FibreSeparates g π q t a C ∧
        linForm a ∉ C.point.asHomogeneousIdeal) ∧
      ∀ y, linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal →
        ∃ C ∈ fibreCurves g π q t, fibrePsi g π q t y ∈ closure ({C.point} : Set _) := by
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  obtain ⟨hψp, hFprop, hdimF, -, hcover, hclass⟩ :=
    fibre_facts sS sY hS hY g hg hgY π q hπq hdim t ht
  haveI := hFprop
  haveI : LocallyOfFiniteType (π.fiberι t ≫ π ≫ sS) := hFprop.toLocallyOfFiniteType
  haveI : QuasiCompact (π.fiberι t ≫ π ≫ sS) :=
    @instQuasiCompactOfUniversallyClosed _ _ _ hFprop.toUniversallyClosed
  haveI : IsLocallyNoetherian (π.fiber t) :=
    LocallyOfFiniteType.isLocallyNoetherian (π.fiberι t ≫ π ≫ sS)
  haveI : CompactSpace (π.fiber t) :=
    QuasiCompact.compactSpace_of_compactSpace (π.fiberι t ≫ π ≫ sS)
  haveI : AlgebraicGeometry.IsNoetherian (π.fiber t) := AlgebraicGeometry.IsNoetherian.mk
  set ψ := fibrePsi g π q t
  have hfinC := finite_fibreCurves sS sY hS hY g hg hgY π q hπq hdim t ht
  have hassF : (Stacks.Divisors.schemeAssociatedPoints (π.fiber t)).Finite :=
    Stacks.Divisors.finite_schemeAssociatedPoints _
  let B₀ : Set (AlgebraicGeometry.Proj (polyGrading k N)) :=
    ψ '' Stacks.Divisors.schemeAssociatedPoints (π.fiber t)
  let B₁ : Set (AlgebraicGeometry.Proj (polyGrading k N)) :=
    ⋃ C ∈ fibreCurves g π q t, ⋃ C' ∈ fibreCurves g π q t, ⋃ (_ : C ≠ C'),
      {p | p ∈ closure ({C.point} : Set _) ∧ p ∈ closure ({C'.point} : Set _)}
  have hB₁ : B₁.Finite :=
    hfinC.biUnion fun C _ => hfinC.biUnion fun C' _ => Set.finite_iUnion fun hne =>
      (finite_inter_of_ne C C' hne).1
  obtain ⟨a, ha⟩ := exists_linForm_notMem (B₀ ∪ B₁) ((hassF.image _).union hB₁)
  have hreg : FibreRegular g π q t a := fun ζ hζ => ha _ (Or.inl ⟨ζ, hζ, rfl⟩)
  obtain ⟨-, hZcl, -⟩ := fibreZero_facts sS sY hS hY g hg hgY π q hπq hdim t ht a hreg
  have hcomp : ∀ ξ ∈ fibreComponents π t, ξ ∈ Stacks.Divisors.schemeAssociatedPoints (π.fiber t) :=
    fun ξ hξ => mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent _ hξ
      (isGenericPoint_closure)
  -- the component through a point of the hyperplane maps onto a curve containing the point
  have hcurveξ : ∀ y ξ, ξ ∈ fibreComponents π t → ξ ⤳ y →
      linForm a ∈ (ψ y).asHomogeneousIdeal →
      ∃ hξc : Mori.IsProperCurve (projToSpecCoeff k N) (ψ ξ),
        ψ y ∈ closure ({ψ ξ} : Set _) := by
    intro y ξ hξ hξy hy
    have hsp : ψ ξ ⤳ ψ y := hξy.map (fibrePsi g π q t).continuous
    rcases hclass ξ hξ with hcl | hcurve
    · exfalso
      have : ψ y = ψ ξ := hcl.closure_subset (specializes_iff_mem_closure.mp hsp)
      exact ha _ (Or.inl ⟨ξ, hcomp ξ hξ, rfl⟩) (this ▸ hy)
    · exact ⟨hcurve, specializes_iff_mem_closure.mp hsp⟩
  refine ⟨a, hreg, fun C hC => ⟨?_, ?_⟩, fun y hy => ?_⟩
  · intro y ξ hyC hya hξy hξ
    obtain ⟨hξc, hyξ⟩ := hcurveξ y ξ hξ hξy hya
    let C' : Mori.ProperCurve (projToSpecCoeff k N) := ⟨ψ ξ, hξc⟩
    have hC' : C' ∈ fibreCurves g π q t := ⟨ξ, rfl⟩
    by_contra hne
    have hne' : C ≠ C' := fun h => hne (by rw [h])
    exact ha _ (Or.inr (Set.mem_biUnion hC (Set.mem_biUnion hC' (Set.mem_iUnion.2
      ⟨hne', hyC, hyξ⟩)))) hya
  · obtain ⟨ξ, hξ, hξC⟩ :=
      exists_fibreComponent_of_mem_fibreCurves sS sY hS hY g hg hgY π q hπq hdim t ht C hC
    rw [← hξC]
    exact ha _ (Or.inl ⟨ξ, hcomp ξ hξ, rfl⟩)
  · obtain ⟨ξ, hξ, hξy⟩ := hcover y
    obtain ⟨hξc, hyξ⟩ := hcurveξ y ξ hξ hξy hy
    exact ⟨⟨ψ ξ, hξc⟩, ⟨ξ, rfl⟩, hyξ⟩

end FibreChow

end CoreLemmas

end Defs

end MMP.Chow.DeterminantCurveForm
