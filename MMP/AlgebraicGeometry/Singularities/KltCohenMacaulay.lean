module

public import MMP.AlgebraicGeometry.CohenMacaulay.NegativeTwistVanishing
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Vanishing.KltPullbackInjective
public import MMP.AlgebraicGeometry.Vanishing.NegativePullbackAmple

/-!
# Projective klt varieties are Cohen–Macaulay

Let `(X, Δ)` be a klt pair with `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective. Then `X` is Cohen–Macaulay.

Take a projective log resolution `f : Y ⟶ X` of `(X, Δ)`, an ample Cartier divisor `L` on `X` and
`n = dim X`. For `i < n` and `r > 0` the group `H^i(Y, 𝒪_Y(-r f^*L))` vanishes, and the pull-back
`H^i(X, 𝒪_X(-rL)) ⟶ H^i(Y, 𝒪_Y(-r f^*L))` is injective
(`MMP.Mori.injective_derivedCohomologyOverField_pullback_divisorialSheaf_of_isKltPair`), so
`H^i(X, 𝒪_X(-rL)) = 0`; the criterion
`MMP.Mori.isCMSheaf_of_eventually_subsingleton_sheafCohomology_tensorPowModule_neg` then shows
that `𝒪_X` is Cohen–Macaulay.

## Main results

* `MMP.Mori.isCMScheme_of_isKltPair`: a projective klt pair `(X, Δ)` with `Δ ≥ 0` has `X`
  Cohen–Macaulay.

## Implementation notes

* `X` carries its structure morphism `sX : X ⟶ Spec k`; "projective over `k`" is
  `MMP.Mori.IsProjectiveVariety k sX`.
* Cohen–Macaulayness is `MMP.Mori.IsCMScheme`: every stalk `𝒪_{X,x}` is a Cohen–Macaulay module
  over itself.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], proof of
  Theorem 5.22.
-/

@[expose] public section

section

/-!
## Proof: Projective klt varieties are Cohen–Macaulay

Let `(X, Δ)` be a klt pair with `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ ≥ 0`. Then `X` is Cohen–Macaulay [KollarMori1998, Thm. 5.22].

Take a projective log resolution `f : Y ⟶ X` of `(X, Δ)`, an ample Cartier divisor `D` on `X`
with pull-back `B = f^*D`, and `n = dim X`. For `r > 0` and `i < n` the group
`H^i(Y, 𝒪_Y(-rB))` vanishes (Kawamata–Viehweg on `Y`), and the pull-back
`H^i(X, 𝒪_X(-rD)) ⟶ H^i(X, Rf_* f^*𝒪_X(-rD))` is injective because `(X, Δ)` is klt. By Leray,
`H^i(X, Rf_* f^*𝒪_X(-rD)) = H^i(Y, f^*𝒪_X(-rD)) = H^i(Y, 𝒪_Y(-rB))`, so
`H^i(X, 𝒪_X(-rD)) = 0`. Since `𝒪_X(-rD) ≅ 𝒪_X ⊗ 𝒪_X(D)^{⊗(-r)}`, the vanishing criterion for
negative twists [KollarMori1998, Cor. 5.72] shows that `𝒪_X` is Cohen–Macaulay.

## Main results

* `MMP.Mori.isCMScheme_of_isKltPair`: a projective klt pair `(X, Δ)` with `Δ ≥ 0`
  has `X` Cohen–Macaulay.

## Implementation notes

The vanishing on `Y` and the injectivity on `X` are stated for the hypercohomology
`H^i(X, -[0])` of `RΓ(X, -) : D(𝒪_X) ⥤ D(k)`, while the criterion of Cor. 5.72 is stated for the
derived functors of `Γ(X, -)` on abelian sheaves; the two agree on sheaves placed in degree zero.
The invertible sheaf of the criterion is `𝒪_X(D)`; its ampleness in the sense of a very ample
power is deduced from ampleness in the sense of [Stacks, Tag 01PS] through the immersion into
projective space of Tag 01VT. The existence of the projective log resolution is the
snc-preserving resolution of the reduced divisor `Supp Δ` (Kollár, Thm. 3.36).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], proof of
  Theorem 5.22 and Corollary 5.72.
-/

namespace MMP.FourfoldProofs.Km5dKltProjectiveCmProof

open CategoryTheory AlgebraicGeometry MonoidalCategory MMP.Mori
open scoped Stacks.SmallDerivedModel

/-- A variety over a field is locally Noetherian and quasi-compact. -/
private theorem isLocallyNoetherian_and_compactSpace {k : Type} [Field k] {Y : Scheme.{0}}
    (s : Y ⟶ Spec (.of k)) (h : AlgebraicGeometry.IsVariety k s) :
    IsLocallyNoetherian Y ∧ CompactSpace Y :=
  have := h.toLocallyOfFiniteType
  have := h.toQuasiCompact
  ⟨LocallyOfFiniteType.isLocallyNoetherian s, QuasiCompact.compactSpace_of_compactSpace s⟩

/-- A projective variety carries an ample Cartier divisor: a Stacks-ample invertible sheaf has a
positive power with a regular section, whose divisor is Cartier with ample divisorial sheaf. -/
private theorem exists_isAmple {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sY]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] :
    ∃ (H : MMP.Mori.Divisor Y) (hH : H.IsCartier), H.IsAmple hH := by
  haveI hYi : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  have hYqp : Stacks.HProjective.IsHQuasiProjective sY :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sY).isProjective.isHQuasiProjective
  obtain ⟨-, L, hLinv, hLamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sY hYqp
  have hL : Stacks.Ample.IsAmple Y L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY L hLamp
  obtain ⟨IX, hIX, -, -, n, hn, ⟨eX⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint Y))
  obtain ⟨H, -, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor IX hIX
  haveI := hHc.isInvertibleModule_divisorialSheaf
  exact ⟨H, hHc, (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)⟩

/-- On a proper scheme over a field `F`, an invertible sheaf that is ample in the sense of
[Stacks, Tag 01PS] is ample in the sense of `MMP.Intersection.IsAmple`: a power of it gives an
immersion into projective space over `F` (Tag 01VT). -/
private theorem isAmple_of_isAmple (F : Type) [Field F]
    {X : Scheme.{0}} [X.Over (Spec (.of F))] [IsProper (X ↘ Spec (.of F))]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.Ample.IsAmple X L) : MMP.Intersection.IsAmple F L := by
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  obtain ⟨d₀, hd₀, himm⟩ :=
    ((Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of F)) L).out 1 6).1 hL
  obtain ⟨eP⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X L d₀
  exact ⟨d₀, hd₀, MMP.Resolution.Bridges.isVeryAmple_of_hasImmersionTwistOver F _ _ eP
    (himm d₀ le_rfl)⟩

/-- Inverses in a monoidal category are unique: if `A ⊗ M ≅ 𝟙` and `M ⊗ B ≅ 𝟙` then `A ≅ B`. -/
private def isoOfTensorIsoUnit {C : Type*} [Category C] [MonoidalCategory C] {A B M : C}
    (e₁ : A ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ B ≅ 𝟙_ C) : A ≅ B :=
  (ρ_ A).symm ≪≫ whiskerLeftIso A e₂.symm ≪≫ (α_ A M B).symm ≪≫ whiskerRightIso e₁ B ≪≫ λ_ B

/-- For a Cartier divisor `H` and `n : ℕ`, `𝒪_X(H)^{⊗n} ≅ 𝒪_X(nH)`. -/
private theorem nonempty_tensorPowModule_iso {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (H : Divisor X) (hH : H.IsCartier) [Stacks.Ample.IsInvertibleModule X H.divisorialSheaf]
    (n : ℕ) :
    Nonempty (Stacks.Ample.tensorPowModule X H.divisorialSheaf (n : ℤ) ≅
      ((n : ℤ) • H).divisorialSheaf) := by
  induction n with
  | zero => exact ⟨Stacks.Ample.tensorPowModuleZeroIso X _ ≪≫
      (Divisor.divisorialSheafZeroIso (X := X)).symm ≪≫ eqToIso (by simp)⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; ring) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X _ (n : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e (Stacks.Ample.tensorPowModuleOneIso X _) ≪≫
      (hH.zsmul _).divisorialSheafTensorIso hH ≪≫
      eqToIso (by congr 1; push_cast; simp only [add_smul, one_smul])⟩

/-- For a Cartier divisor `H` and `n : ℕ`, `𝒪_X(H)^{⊗(-n)} ≅ 𝒪_X(-nH)`: both are inverse to
`𝒪_X(H)^{⊗n} ≅ 𝒪_X(nH)`. -/
private theorem nonempty_tensorPowModule_neg_iso {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (H : Divisor X) (hH : H.IsCartier) [Stacks.Ample.IsInvertibleModule X H.divisorialSheaf]
    (n : ℕ) :
    Nonempty (Stacks.Ample.tensorPowModule X H.divisorialSheaf (-(n : ℤ)) ≅
      (-((n : ℤ) • H)).divisorialSheaf) := by
  obtain ⟨e⟩ := nonempty_tensorPowModule_iso H hH n
  refine ⟨isoOfTensorIsoUnit (M := ((n : ℤ) • H).divisorialSheaf) ?_ ?_⟩
  · exact whiskerLeftIso _ e.symm ≪≫ Stacks.Ample.tensorPowModuleAddIso X _ _ _ ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by ring) ≪≫
      Stacks.Ample.tensorPowModuleZeroIso X _
  · exact (hH.zsmul _).divisorialSheafTensorIso (hH.zsmul _).neg ≪≫ eqToIso (by simp) ≪≫
      Divisor.divisorialSheafZeroIso (X := X)

/-- Vanishing of the hypercohomology `H^i(X, F[0])` over `k` implies vanishing of the sheaf
cohomology `H^i(X, F)` of the underlying abelian sheaf. -/
private theorem subsingleton_sheafCohomology {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (F : X.Modules) (i : ℕ)
    (h : Subsingleton (Stacks.Duality.derivedCohomologyOverField sX
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) i)) :
    Subsingleton (Sheaf.H.{0} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) i) := by
  have h : Subsingleton (((SheafOfModules.evaluation X.ringCatSheaf
      (Opposite.op ⊤)).rightDerived i).obj F) :=
    (ConcreteCategory.bijective_of_isIso
      (Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField k sX F i).hom).1.subsingleton
  exact (MMP.Cohomology.subsingleton_sheafH_iff F i).2 h

/-- **Leray**: `RΓ(X, Rf_* -) ≅ RΓ(Y, -)` over `k`, for `f : Y ⟶ X` and `X` over `k`. -/
private noncomputable def lerayIso {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) :
    Stacks.Duality.derivedPushforward f ⋙ derivedGlobalSectionsOver sX ≅
      derivedGlobalSectionsOver (f ≫ sX) :=
  Functor.isoWhiskerLeft _ (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k sX) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.Duality.derivedPushforwardCompIso f sX) _ ≪≫
    (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k (f ≫ sX)).symm

/-- If the pull-back `H^i(X, 𝒪_X(D)) ⟶ H^i(X, Rf_* f^*𝒪_X(D))` is injective and
`H^i(Y, 𝒪_Y(f^*D)) = 0`, then `H^i(X, 𝒪_X(D)) = 0`. -/
private theorem subsingleton_of_injective {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y] [CompactSpace Y]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) (D : Divisor X) (hD : D.IsCartier)
    (hDf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    (B : Divisor Y) (hB : D.IsPullback f hDf B) (i : ℤ)
    (hinj : let F := D.divisorialSheaf
      let G := (Scheme.Modules.pullback f).obj F
      let c : (DerivedCategory.singleFunctor X.Modules 0).obj
            ((Scheme.Modules.pushforward f).obj G) ⟶
          (Stacks.Duality.derivedPushforward f).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj G) :=
        (Stacks.DerivedFunctor.mapSingleQhIso (Scheme.Modules.pushforward f) 0).inv.app G ≫
          ((Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
              ((HomotopyCategory.singleFunctor Y.Modules 0).obj G) ≫
          (Stacks.Duality.derivedPushforward f).map
            ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app G)
      Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).map
        ((derivedGlobalSectionsOver sX).map
          ((DerivedCategory.singleFunctor X.Modules 0).map
            ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) ≫ c))).hom)
    (hvan : Subsingleton (Stacks.Duality.derivedCohomologyOverField (f ≫ sX)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj B.divisorialSheaf) i)) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField sX
      ((DerivedCategory.singleFunctor X.Modules 0).obj D.divisorialSheaf) i) := by
  let G := (Scheme.Modules.pullback f).obj D.divisorialSheaf
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).obj
      ((derivedGlobalSectionsOver sX).obj ((Stacks.Duality.derivedPushforward f).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G))) ≅
      Stacks.Duality.derivedCohomologyOverField (f ≫ sX)
        ((DerivedCategory.singleFunctor Y.Modules 0).obj B.divisorialSheaf) i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).mapIso
      ((lerayIso sX f).app _ ≪≫ (derivedGlobalSectionsOver (f ≫ sX)).mapIso
        ((DerivedCategory.singleFunctor Y.Modules 0).mapIso (hB.divisorialSheafIso (hBc := hD)).symm))
  have := (ConcreteCategory.bijective_of_isIso e.hom).1.subsingleton
  exact hinj.subsingleton

section LogResolution

open TopologicalSpace MMP.Resolution
open AlgebraicGeometry hiding PrimeDivisor

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-- **Projective log resolutions exist** in characteristic zero: the snc-preserving log resolution
of the reduced divisor `Supp D` is a projective log resolution of `(X, D)`. -/
private theorem exists_isLogResolution_isProjective {k : Type} [Field k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (D : RDivisor X) :
    ∃ (Y : Scheme.{0}) (g : Y ⟶ X), MMP.Mori.IsLogResolution sX D g ∧
      AlgebraicGeometry.IsProjective g ∧ AlgebraicGeometry.IsVariety k (g ≫ sX) := by
  obtain ⟨Y, f, hres, hpure, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX D.support
  have hYv : AlgebraicGeometry.IsVariety k (f ≫ sX) := hres.isVariety_source
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_compactSpace _ hYv
  have : AlgebraicGeometry.IsNoetherian Y := {}
  have hsupp_eq : (D.supp : Set X) = D.support.sup fun E => (E.idealSheaf.support : Set X) := by
    rw [DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
    rfl
  rw [← hsupp_eq] at hS
  refine ⟨Y, f, ⟨⟨hres.isProjective.isProper, hres.isBirationalMorphism, hres.isSmoothScheme⟩,
    hpure, isSNCSubset_of_isSNCClosedSubset _ ?_⟩, hres.isProjective, hYv⟩
  simpa using hS

end LogResolution

/-- In an irreducible space, every irreducible component of the subspace `univ` has the
dimension of the space. -/
private theorem topologicalKrullDim_of_mem_irreducibleComponents_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (S : Set T) (hS : S = Set.univ) (Z : Set S)
    (hZ : Z ∈ irreducibleComponents S) : topologicalKrullDim Z = topologicalKrullDim T := by
  subst hS
  haveI : IrreducibleSpace (Set.univ : Set T) := ((Homeomorph.Set.univ T).irreducibleSpace_iff).2 inferInstance
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
  subst hZ
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ T).isHomeomorph]

/-- The support of `𝒪_X` is all of `X`. -/
private theorem setOf_nontrivial_stalk_unit (X : Scheme.{0}) :
    {x : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{0})
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x)} = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    (Stacks.Ample.unitStalkEquiv X x).toEquiv.nontrivial

/-- **KM Cor. 5.72 for `𝒪_X`.** If `X` is a projective variety of dimension `n` and `D` is an
ample Cartier divisor with `H^i(X, 𝒪_X(-rD)) = 0` for `i < n` and `r > 0`, then `X` is
Cohen–Macaulay. -/
private theorem isCMScheme_of_subsingleton {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : Divisor X) (hDc : D.IsCartier) (hD : D.IsAmple hDc)
    (hvan : ∀ r : ℕ, 0 < r → ∀ i : ℕ, i < n →
      Subsingleton (Stacks.Duality.derivedCohomologyOverField sX
        ((DerivedCategory.singleFunctor X.Modules 0).obj (-((r : ℤ) • D)).divisorialSheaf) i)) :
    IsCMScheme X := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have hX : IsProjectiveMorphism (X ↘ Spec (.of k)) :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sX).isProjective
  haveI := hDc.isInvertibleModule_divisorialSheaf
  haveI : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hX
  have hL : MMP.Intersection.IsAmple k D.divisorialSheaf := isAmple_of_isAmple k _ hD
  refine isCMSheaf_of_eventually_subsingleton_sheafCohomology_tensorPowModule_neg k hX
    D.divisorialSheaf hL n _ (fun Z hZ => ?_) (Filter.eventually_atTop.2 ⟨1, fun r hr i hi => ?_⟩)
  · rw [topologicalKrullDim_of_mem_irreducibleComponents_univ _
      (setOf_nontrivial_stalk_unit X) Z hZ, hn]
  · obtain ⟨e⟩ := nonempty_tensorPowModule_neg_iso D hDc r
    have h := subsingleton_sheafCohomology sX _ i (hvan r hr i hi)
    let e' := (Sheaf.functorH.{0} (Opens.grothendieckTopology X) i).mapIso
      ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso
        (MonoidalCategory.leftUnitor (C := X.Modules) _ ≪≫ e))
    exact e'.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.2 h

end MMP.FourfoldProofs.Km5dKltProjectiveCmProof

end

section

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km5dKltProjectiveCmProof in
open scoped Stacks.SmallDerivedModel in
/-- Let `(X, Δ)` be a klt pair with `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective. Then `X` is Cohen–Macaulay. -/
@[mmp "lem_km5d_klt_projective_cm"]
public theorem isCMScheme_of_isKltPair {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : 0 ≤ Δ) :
    IsCMScheme X := by
  have hXn : IsNormalVariety k sX := hklt.1.1
  have hn : topologicalKrullDim X = n := hklt.1.2.1.topologicalKrullDim_eq
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_compactSpace sX
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sX).toIsVariety
  obtain ⟨D, hDc, hD⟩ := exists_isAmple sX
  obtain ⟨Y, f, hres, hproj, hYv⟩ :=
    exists_isLogResolution_isProjective sX hXn (QDivisor.toRDivisor Δ)
  have : IsIntegral Y := hYv.toIsIntegral
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_compactSpace _ hYv
  haveI : IsNormal Y :=
    (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      hres.isSmoothScheme).2
  haveI : IsDominant f := hres.isBirationalMorphism.isDominant
  have hDf (E : Divisor X) : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ E.supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f E
  obtain ⟨B, hB⟩ := hDc.exists_isPullback (hDf D)
  refine isCMScheme_of_subsingleton sX hn D hDc hD fun r hr i hi => ?_
  have hB' : (-((r : ℤ) • D)).IsPullback f (hDf _) (-((r : ℤ) • B)) := by
    have h := hB.zsmul hDc (-(r : ℤ)) (hDf _)
    rwa [neg_smul, neg_smul] at h
  exact subsingleton_of_injective sX f _ (hDc.zsmul _).neg (hDf _) _ hB' i
    (injective_derivedCohomologyOverField_pullback_divisorialSheaf_of_isKltPair sX hklt hΔ f hres
      hproj _ (hDc.zsmul _).neg i)
    (subsingleton_derivedCohomologyOverField_divisorialSheaf_neg_zsmul_pullback sX hn f
      hres.toIsSmoothResolution hproj D hDc hD (hDf D) B hB r hr i (by exact_mod_cast hi))

end MMP.Mori

end

end
