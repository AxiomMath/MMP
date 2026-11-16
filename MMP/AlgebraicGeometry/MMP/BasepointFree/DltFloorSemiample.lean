module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
import MMP.AlgebraicGeometry.MMP.BasepointFree.DltFloorSectionLifting
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Preimage
import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor

/-!
# Semiampleness from a semiample restriction to the whole dlt floor

Let `(X, B)` be a `ℚ`-factorial dlt pair with `ℚ`-boundary `B`, projective over a projective
complex variety `Z` by `f`, and put `D = K_X + B` and `T = ⌊B⌋`, the whole reduced union of the
components of coefficient one. Suppose that `P ≥ 0` is a `ℚ`-Cartier divisor with
`Supp P = Supp T` and that `D - εP` is semiample over `Z` for every sufficiently small rational
`ε > 0`. If moreover `D|_T` is semiample over `Z`, then `D` is semiample over `Z`.

Off `T` the sections come from free multiples of `D - εP` times the canonical section of `εP`;
along `T` the floor sections are lifted by the surjectivity of
`f_* 𝒪_X(mD) → f_* 𝒪_T(mD)` for the whole dlt floor.

## Main results

* `MMP.Fourfold.QDivisor.isRelativelySemiample_of_isDltPair_of_restrict_roundDown`: the
  proposition above.

## Implementation notes

* `T` is the reduced closed subscheme `B.roundDown.suppScheme` on `Supp ⌊B⌋`, with closed
  immersion `ι = B.roundDown.suppIdeal.subschemeι`.
* Semiampleness of `D|_T` over `Z` is read on line bundles: some positive multiple `mD` is a
  Cartier divisor `E` and the pull-back `ι^* 𝒪_X(E)` is generated over `Z` by the morphism
  `ι ≫ f`, that is, the counit `(ι ≫ f)^* (ι ≫ f)_* ι^* 𝒪_X(E) → ι^* 𝒪_X(E)` is an epimorphism.
* "Sufficiently small positive rational `ε`" is the filter `𝓝[>] 0` on `ℚ`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

@[expose] public noncomputable section

open Opposite

namespace MMP.SemiampleFloorUnionCriterion

open MMP.Mori MMP.Fourfold

/-- A finitely supported `ℚ`-valued function has a common denominator. -/
private theorem exists_pos_nsmul_intCast {α : Type*} (c : α →₀ ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∀ a, ∃ n : ℤ, ((d : ℚ) • c) a = n := by
  classical
  refine ⟨∏ a ∈ c.support, (c a).den, Finset.prod_pos fun a _ => (c a).den_pos, fun a => ?_⟩
  by_cases ha : a ∈ c.support
  · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun a => (c a).den) ha
    refine ⟨(c a).num * r, ?_⟩
    rw [Finsupp.smul_apply, smul_eq_mul, hr]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  · exact ⟨0, by simp [Finsupp.notMem_support_iff.mp ha]⟩

section Bookkeeping

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The coefficient along `P` of the Weil divisor of a `ℚ`-Cartier divisor `∑ a_E E`. -/
private def weilCoeff (P : MMP.Mori.PrimeDivisor X) : KCartierDivisor ℚ X →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun E => (MMP.Intersection.primeDivisorOrder P E : ℚ)

private theorem weilCoeff_apply (P : MMP.Mori.PrimeDivisor X) (c : KCartierDivisor ℚ X) :
    weilCoeff P c = c.sum fun E a => a * (MMP.Intersection.primeDivisorOrder P E : ℚ) := by
  rw [weilCoeff, Finsupp.linearCombination_apply]
  rfl

/-- The order along `P` of the realization of an integral `ℚ`-Cartier divisor is its Weil
coefficient. -/
private theorem primeDivisorOrder_realization (c : KCartierDivisor ℚ X)
    (h : ∀ E, ∃ n : ℤ, c E = n) (P : MMP.Mori.PrimeDivisor X) :
    (MMP.Intersection.primeDivisorOrder P (KCartierDivisor.realization c h) : ℚ) =
      weilCoeff P c := by
  rw [KCartierDivisor.realization, map_finsuppSum, weilCoeff_apply]
  push_cast
  refine Finset.sum_congr rfl fun E _ => ?_
  dsimp only
  rw [map_zsmul, smul_eq_mul]
  push_cast
  rw [← (h E).choose_spec]

/-- A `ℚ`-divisor `Q` with the coefficients of an integral `ℚ`-Cartier divisor `c` is the Weil
divisor of the realization of `c`. -/
private theorem exists_isWeilDivisorOfCartier_realization (c : KCartierDivisor ℚ X)
    (h : ∀ E, ∃ n : ℤ, c E = n) (Q : QDivisor X) (hQ : ∀ P, Q.coeff P = weilCoeff P c) :
    ∃ w : Divisor X, Divisor.toQDivisor w = Q ∧
      MMP.Intersection.IsWeilDivisorOfCartier (KCartierDivisor.realization c h) w := by
  have hint : ∀ P, ∃ n : ℤ, Q.coeff P = n := fun P =>
    ⟨_, (hQ P).trans (primeDivisorOrder_realization c h P).symm⟩
  obtain ⟨w, hw⟩ := (QDivisor.mem_range_toQDivisor_iff Q).mpr hint
  refine ⟨w, hw, fun P => ?_⟩
  have h1 : (w.coeff P : ℚ) =
      (MMP.Intersection.primeDivisorOrder P (KCartierDivisor.realization c h) : ℚ) := by
    rw [← Divisor.coeff_toQDivisor, hw, hQ, primeDivisorOrder_realization]
  rw [show w.coeff P = _ from Int.cast_injective h1]
  exact MMP.Intersection.isOrderAlong_primeDivisorOrder _ P

end Bookkeeping

/-! ### Relative freeness, Cartier and Weil -/

section Freeness

variable {X Z : Scheme.{0}}

/-- The counit of `f^* ⊣ f_*` is an epimorphism at `G` once it is one at an isomorphic `F`. -/
private theorem epi_counit_of_iso (f : X ⟶ Z) {F G : X.Modules} (e : F ≅ G)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G) := by
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).counit.naturality e.inv
  simp only [Functor.id_map] at hn
  have : (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map e.inv ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F ≫ e.hom := by
    rw [← Category.assoc, hn, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [this]
  infer_instance

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

private theorem isRelativelyFreeDivisor_of_isRelativelyFreeCartier (f : X ⟶ Z)
    {R : X.CartierDivisor} {w : Divisor X} (hw : MMP.Intersection.IsWeilDivisorOfCartier R w)
    (h : IsRelativelyFreeCartier f R) : IsRelativelyFreeDivisor f w :=
  epi_counit_of_iso f hw.nonempty_sheaf_iso_divisorialSheaf.some h

private theorem isRelativelyFreeCartier_of_isRelativelyFreeDivisor (f : X ⟶ Z)
    {R : X.CartierDivisor} {w : Divisor X} (hw : MMP.Intersection.IsWeilDivisorOfCartier R w)
    (h : IsRelativelyFreeDivisor f w) : IsRelativelyFreeCartier f R :=
  epi_counit_of_iso f hw.nonempty_sheaf_iso_divisorialSheaf.some.symm h

/-- A relatively free realization of `N • C`, with `C` a `ℚ`-Cartier divisor whose Weil
divisor is `D`, makes `D` semiample over `Z`. -/
private theorem isRelativelySemiample_of_isRelativelyFreeDivisor (f : X ⟶ Z) (D : QDivisor X)
    (C : KCartierDivisor ℚ X) (hC : ∀ P, D.coeff P = weilCoeff P C) {N : ℕ} (hN : 0 < N)
    (hint : ∀ E, ∃ n : ℤ, ((N : ℚ) • C) E = n) {W : Divisor X}
    (hW : MMP.Intersection.IsWeilDivisorOfCartier (KCartierDivisor.realization _ hint) W)
    (hfree : IsRelativelyFreeDivisor f W) : MMP.Fourfold.QDivisor.IsRelativelySemiample f D :=
  ⟨C, fun P => (hC P).trans (weilCoeff_apply P C), N, hN, hint,
    isRelativelyFreeCartier_of_isRelativelyFreeDivisor f hW hfree⟩

end Freeness

/-! ### Pointwise generation -/

section Pointwise

variable {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- `W` is generated at `x` by a section over the preimage of a neighbourhood of `f x`: a unit
`ψ` of `K(X)` with `W + div ψ` effective over `f⁻¹U` and zero along the prime divisors
through `x`. -/
private def IsGeneratedAt (f : X ⟶ Z) (W : Divisor X) (x : X) : Prop :=
  ∃ (U : Z.Opens) (_ : f x ∈ U) (ψ : (RationalFunctions X)ˣ),
    (∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty → 0 ≤ W.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor X, x ∈ P.support → W.coeff P + P.ord ψ = 0

/-- If `ψ` generates `w` at `x`, then `ψ^k` generates `k w + G` for an effective `G` vanishing
along the prime divisors through `x`. -/
private theorem IsGeneratedAt.nsmul_add {f : X ⟶ Z} {w : Divisor X} {x : X}
    (h : IsGeneratedAt f w x) (k : ℕ) {G : Divisor X} (hG : ∀ P, 0 ≤ G.coeff P)
    (hGx : ∀ P : MMP.Mori.PrimeDivisor X, x ∈ P.support → G.coeff P = 0) :
    IsGeneratedAt f ((k : ℤ) • w + G) x := by
  obtain ⟨U, hU, ψ, h1, h2⟩ := h
  have key : ∀ P : MMP.Mori.PrimeDivisor X, ((k : ℤ) • w + G).coeff P + P.ord (ψ ^ k) =
      k * (w.coeff P + P.ord ψ) + G.coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, PrimeDivisor.ord_pow,
      smul_eq_mul, nsmul_eq_mul]
    ring
  refine ⟨U, hU, ψ ^ k, fun P hP => ?_, fun P hP => ?_⟩
  · rw [key]
    exact add_nonneg (mul_nonneg (Int.natCast_nonneg k) (h1 P hP)) (hG P)
  · rw [key, h2 P hP, hGx P hP, mul_zero, add_zero]

end Pointwise

/-! ### Relative germs -/

section RelativeGerms

/-- The submodule of the stalk `L_y` spanned by the germs of the sections of `L` over the
preimages `g⁻¹U` of the opens `U ∋ g y`. -/
private def relSpan {Y Z : Scheme.{0}} (g : Y ⟶ Z) (L : Y.Modules) (y : Y) :
    Submodule (Y.presheaf.stalk y) ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L) :=
  Submodule.span _ {m | ∃ (U : Z.Opens) (hU : y ∈ g ⁻¹ᵁ U) (s : Γ(L, g ⁻¹ᵁ U)),
    (L.presheaf.germ (g ⁻¹ᵁ U) y hU).hom s = m}

/-- Relative generation spans every stalk by relative germs. -/
private theorem relSpan_eq_top_of_epi {Y Z : Scheme.{0}} (g : Y ⟶ Z) (L : Y.Modules)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app L)) (y : Y) :
    relSpan g L y = ⊤ := by
  set N := relSpan g L y
  let A : ModuleCat.{0} (Y.presheaf.stalk y) :=
    ModuleCat.of _ (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L) ⧸ N)
  let q : (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L ⟶ A :=
    ModuleCat.ofHom (X := ↑((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L)) N.mkQ
  let hq : L ⟶ Stacks.ModuleSkyscraper.skyModules Y y A :=
    ⟨Stacks.ModuleSkyscraper.toSky (R := Y.presheaf) (x := y) (M := L.val) q⟩
  let h0 : L ⟶ Stacks.ModuleSkyscraper.skyModules Y y A :=
    ⟨Stacks.ModuleSkyscraper.toSky (R := Y.presheaf) (x := y) (M := L.val) 0⟩
  have hgh : hq = h0 := by
    refine eq_of_epi_counit_of_pushforward_map_eq g h ?_
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext s
    funext p
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨U, p.down, s, rfl⟩)
  rw [eq_top_iff]
  intro m _
  obtain ⟨U, hU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq L.presheaf m
  exact (Submodule.Quotient.mk_eq_zero N).mp <| congrArg
    (fun k : L ⟶ Stacks.ModuleSkyscraper.skyModules Y y A => (k.val.app (op U)).hom m₀ ⟨hU⟩) hgh

/-- Spanning by relative germs is invariant under isomorphism. -/
private theorem relSpan_eq_top_of_iso {Y Z : Scheme.{0}} (g : Y ⟶ Z) {P P' : Y.Modules}
    (e : P ≅ P') (y : Y) (h : relSpan g P y = ⊤) : relSpan g P' y = ⊤ := by
  have key : ∀ w ∈ relSpan g P y,
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map e.hom).hom w ∈ relSpan g P' y := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨U, hU, s, rfl⟩ := hw
      exact (congrArg (fun w => w ∈ relSpan g P' y)
        (Stacks.Modules.stalkLinearMap_germ e.hom.val _ hU s)).mpr
          (Submodule.subset_span ⟨U, hU, _, rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  intro z _
  have := key (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map e.inv).hom z)
    (h ▸ Submodule.mem_top)
  rwa [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply] at this

/-- Relative germs span a stalk of `L₁ ⊗ L₂` once they span those of `L₁` and of `L₂`: the
stalk is `L₁,y ⊗ L₂,y`, and the product of germs of sections over `g⁻¹U` and `g⁻¹U'` is the
germ of a section over `g⁻¹(U ∩ U')`. -/
private theorem relSpan_tensor_eq_top {Y Z : Scheme.{0}} (g : Y ⟶ Z) (L₁ L₂ : Y.Modules)
    (y : Y) (h₁ : relSpan g L₁ y = ⊤) (h₂ : relSpan g L₂ y = ⊤) :
    relSpan g (Scheme.Modules.tensorObj L₁ L₂) y = ⊤ := by
  set Φ : (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj (Scheme.Modules.tensorObj L₁ L₂) ≅
      MonoidalCategory.tensorObj ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L₁)
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L₂) :=
    (AlgebraicGeometry.tensorStalkEquiv L₁ L₂ y).toModuleIso
  set S := relSpan g (Scheme.Modules.tensorObj L₁ L₂) y
  let P := S.comap Φ.inv.hom
  have hA : ∀ (U U' : Z.Opens) (hU : y ∈ g ⁻¹ᵁ U) (hU' : y ∈ g ⁻¹ᵁ U')
      (s : Γ(L₁, g ⁻¹ᵁ U)) (t : Γ(L₂, g ⁻¹ᵁ U')),
      (L₁.presheaf.germ _ y hU s ⊗ₜ[Y.presheaf.stalk y] L₂.presheaf.germ _ y hU' t) ∈ P := by
    intro U U' hU hU' s t
    have hW : y ∈ g ⁻¹ᵁ (U ⊓ U') := ⟨hU, hU'⟩
    let i : g ⁻¹ᵁ (U ⊓ U') ⟶ g ⁻¹ᵁ U := homOfLE (g.preimage_mono inf_le_left)
    let i' : g ⁻¹ᵁ (U ⊓ U') ⟶ g ⁻¹ᵁ U' := homOfLE (g.preimage_mono inf_le_right)
    have e3 := AlgebraicGeometry.tensorStalkEquiv_germ L₁ L₂ y _ hW (L₁.presheaf.map i.op s)
      (L₂.presheaf.map i'.op t)
    have e3' : Φ.hom.hom (PresheafOfModules.tensorSheafGerm Y.sheaf L₁ L₂ y _ hW
        (L₁.presheaf.map i.op s) (L₂.presheaf.map i'.op t)) =
        L₁.presheaf.germ _ y hU s ⊗ₜ[Y.presheaf.stalk y] L₂.presheaf.germ _ y hU' t := by
      refine e3.trans ?_
      rw [TopCat.Presheaf.germ_res_apply L₁.presheaf i y hW s,
        TopCat.Presheaf.germ_res_apply L₂.presheaf i' y hW t]
    refine (congrArg (fun z => Φ.inv.hom z ∈ S) e3').mp ?_
    have hinv : ∀ z, Φ.inv.hom (Φ.hom.hom z) = z := fun z => by
      rw [← ModuleCat.comp_apply, Φ.hom_inv_id, ModuleCat.id_apply]
    exact (congrArg (fun z => z ∈ S) (hinv _)).mpr (Submodule.subset_span ⟨U ⊓ U', hW, _, rfl⟩)
  have hB : ∀ (U' : Z.Opens) (hU' : y ∈ g ⁻¹ᵁ U') (t : Γ(L₂, g ⁻¹ᵁ U'))
      (a : (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L₁),
      (a ⊗ₜ[Y.presheaf.stalk y] L₂.presheaf.germ _ y hU' t) ∈ P := by
    intro U' hU' t a
    have ha : a ∈ relSpan g L₁ y := h₁ ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨U, hU, s, rfl⟩ := ha
      exact hA U U' hU hU' s t
    | zero => rw [TensorProduct.zero_tmul]; exact P.zero_mem
    | add a b _ _ ha hb => rw [TensorProduct.add_tmul]; exact P.add_mem ha hb
    | smul r a _ ha => rw [← TensorProduct.smul_tmul']; exact P.smul_mem r ha
  have hC : ∀ (a : (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L₁)
      (b : (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj L₂),
      (a ⊗ₜ[Y.presheaf.stalk y] b) ∈ P := by
    intro a b
    have hb : b ∈ relSpan g L₂ y := h₂ ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨U', hU', t, rfl⟩ := hb
      exact hB U' hU' t a
    | zero => rw [TensorProduct.tmul_zero]; exact P.zero_mem
    | add b c _ _ hb hc => rw [TensorProduct.tmul_add]; exact P.add_mem hb hc
    | smul r b _ hb => rw [TensorProduct.tmul_smul]; exact P.smul_mem r hb
  rw [eq_top_iff]
  intro z _
  have hz : Φ.hom.hom z ∈ P := by
    induction Φ.hom.hom z using TensorProduct.induction_on with
    | zero => exact P.zero_mem
    | tmul a b => exact hC a b
    | add a b ha hb => exact P.add_mem ha hb
  change Φ.inv.hom (Φ.hom.hom z) ∈ S at hz
  rwa [← ModuleCat.comp_apply, Φ.hom_inv_id, ModuleCat.id_apply] at hz

/-- Relative germs of `ι^* 𝒪_X(E)` spanning give relative germs of `ι^* 𝒪_X(E + E)` spanning,
through `ι^* 𝒪_X(E + E) ≅ ι^* (𝒪_X(E) ⊗ 𝒪_X(E)) ≅ ι^* 𝒪_X(E) ⊗ ι^* 𝒪_X(E)`. -/
private theorem relSpan_pullback_add_eq_top {T X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (ι : T ⟶ X) (f : X ⟶ Z)
    {E : Divisor X} (hE : E.IsCartier) (y : T)
    (h : relSpan (ι ≫ f) ((Scheme.Modules.pullback ι).obj E.divisorialSheaf) y = ⊤) :
    relSpan (ι ≫ f) ((Scheme.Modules.pullback ι).obj (E + E).divisorialSheaf) y = ⊤ := by
  let L := (Scheme.Modules.pullback ι).obj E.divisorialSheaf
  let e : Scheme.Modules.tensorObj L L ≅
      (Scheme.Modules.pullback ι).obj (E + E).divisorialSheaf :=
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso ι E.divisorialSheaf
      E.divisorialSheaf).symm ≪≫ (Scheme.Modules.pullback ι).mapIso (hE.divisorialSheafTensorIso hE)
  exact relSpan_eq_top_of_iso _ e y (relSpan_tensor_eq_top _ L L y h h)

/-- **Lifting relative generation from a closed subscheme.** Let `ι : T ⟶ X` have surjective
stalk maps and `f : X ⟶ Z`. If `f_* F → f_* ι_* ι^* F` is an epimorphism and the relative germs
of `ι^* F` over `Z` span its stalk at `y`, then the relative germs of `F` span its (finitely
generated) stalk at `ι y`. A linear form `F_{ι y} → V` killing the relative germs of `F`, with
`V` a module over `𝒪_{T,y}`, gives a morphism `ι^* F ⟶ 𝒪_T`-skyscraper vanishing on the relative
sections lifted from `X`, hence on all relative sections, hence zero; with
`V = F_{ι y} / (N + I F_{ι y})`, `I` the kernel of the stalk map, Nakayama's lemma concludes. -/
private theorem relSpan_eq_top_of_lift {T X Z : Scheme.{0}} (ι : T ⟶ X) (f : X ⟶ Z)
    (F : X.Modules) (y : T) (hsurj : Function.Surjective (ι.stalkMap y).hom)
    (hlift : Epi ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F)))
    (hT : relSpan (ι ≫ f) ((Scheme.Modules.pullback ι).obj F) y = ⊤)
    (hfg : Module.Finite (X.presheaf.stalk (ι y))
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (ι y)).obj F)) :
    relSpan f F (ι y) = ⊤ := by
  classical
  set φ : X.presheaf.stalk (ι y) →+* T.presheaf.stalk y := (ι.stalkMap y).hom with hφ
  set N := relSpan f F (ι y)
  set I : Ideal (X.presheaf.stalk (ι y)) := RingHom.ker φ with hI
  let M := (Stacks.ModuleSkyscraper.modulesStalkFunctor X (ι y)).obj F
  let Q := ↑M ⧸ N
  let V := Q ⧸ (I • ⊤ : Submodule (X.presheaf.stalk (ι y)) Q)
  let σ : T.presheaf.stalk y ≃+* (X.presheaf.stalk (ι y)) ⧸ I :=
    (RingHom.quotientKerEquivOfSurjective hsurj).symm
  have hσ : ∀ r, σ (φ r) = Ideal.Quotient.mk I r := fun r =>
    (RingHom.quotientKerEquivOfSurjective hsurj).symm_apply_apply (Ideal.Quotient.mk I r)
  letI : Module (T.presheaf.stalk y) V := Module.compHom V σ.toRingHom
  let A : ModuleCat.{0} (T.presheaf.stalk y) := ModuleCat.of _ V
  let q : M ⟶ (ModuleCat.restrictScalars φ).obj A :=
    ModuleCat.ofHom (X := ↑M) (Y := ↑((ModuleCat.restrictScalars φ).obj A))
    { toFun := fun m => (Submodule.Quotient.mk (Submodule.Quotient.mk m : Q) : V)
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change _ = φ r • (Submodule.Quotient.mk (Submodule.Quotient.mk m : Q) : V)
        change _ = σ (φ r) • (Submodule.Quotient.mk (Submodule.Quotient.mk m : Q) : V)
        rw [hσ]
        rfl }
  have hqN : ∀ m ∈ N, q.hom m = 0 := fun m hm => by
    change (Submodule.Quotient.mk (Submodule.Quotient.mk m : Q) : V) = 0
    rw [(Submodule.Quotient.mk_eq_zero N).mpr hm]
    rfl
  let g : F ⟶ Stacks.ModuleSkyscraper.skyModules X (ι y) ((ModuleCat.restrictScalars φ).obj A) :=
    ⟨Stacks.ModuleSkyscraper.toSky (R := X.presheaf) (x := ι y) (M := F.val) q⟩
  let g₀ : F ⟶ Stacks.ModuleSkyscraper.skyModules X (ι y) ((ModuleCat.restrictScalars φ).obj A) :=
    ⟨Stacks.ModuleSkyscraper.toSky (R := X.presheaf) (x := ι y) (M := F.val) 0⟩
  have h1 : (Scheme.Modules.pushforward f).map g = (Scheme.Modules.pushforward f).map g₀ := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext s
    funext p
    exact hqN _ (Submodule.subset_span ⟨U, p.down, s, rfl⟩)
  let e := Stacks.ModuleSkyscraper.pushSkyObjIso ι y A
  let adj := Scheme.Modules.pullbackPushforwardAdjunction ι
  let h : (Scheme.Modules.pullback ι).obj F ⟶ Stacks.ModuleSkyscraper.skyModules T y A :=
    (adj.homEquiv _ _).symm (g ≫ e.inv)
  let h₀ : (Scheme.Modules.pullback ι).obj F ⟶ Stacks.ModuleSkyscraper.skyModules T y A :=
    ⟨Stacks.ModuleSkyscraper.toSky (R := T.presheaf) (x := y)
      (M := ((Scheme.Modules.pullback ι).obj F).val) 0⟩
  have hgh : g ≫ e.inv = adj.unit.app F ≫ (Scheme.Modules.pushforward ι).map h := by
    rw [show g ≫ e.inv = adj.homEquiv _ _ h from (Equiv.apply_symm_apply _ _).symm,
      Adjunction.homEquiv_unit]
  have hgh₀ : g₀ ≫ e.inv = adj.unit.app F ≫ (Scheme.Modules.pushforward ι).map h₀ := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext s
    funext p
    rfl
  have h2 : (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforward ι).map h) =
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforward ι).map h₀) := by
    rw [← cancel_epi ((Scheme.Modules.pushforward f).map (adj.unit.app F)), ← Functor.map_comp,
      ← Functor.map_comp, ← hgh, ← hgh₀, Functor.map_comp, Functor.map_comp, h1]
  have hrel : ∀ (U : Z.Opens) (s : Γ((Scheme.Modules.pullback ι).obj F, (ι ≫ f) ⁻¹ᵁ U))
      (p : PLift (y ∈ (ι ≫ f) ⁻¹ᵁ U)), (h.val.app (op ((ι ≫ f) ⁻¹ᵁ U))).hom s p = 0 := by
    intro U s p
    exact congrArg (fun k : (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pushforward ι).obj
      ((Scheme.Modules.pullback ι).obj F)) ⟶ (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward ι).obj (Stacks.ModuleSkyscraper.skyModules T y A)) =>
          (k.val.app (op U)).hom s p) h2
  let β : (Stacks.ModuleSkyscraper.modulesStalkFunctor T y).obj
      ((Scheme.Modules.pullback ι).obj F) ⟶ A :=
    Stacks.ModuleSkyscraper.fromStalkLinear (R := T.presheaf) (x := y) h.val
  have hβ : ∀ z : (Stacks.ModuleSkyscraper.modulesStalkFunctor T y).obj
      ((Scheme.Modules.pullback ι).obj F), β.hom z = 0 := by
    intro z
    have hz : z ∈ relSpan (ι ≫ f) ((Scheme.Modules.pullback ι).obj F) y := hT ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨U, hU, s, rfl⟩ := hz
      exact (Stacks.ModuleSkyscraper.fromStalkLinear_germ h.val _ hU s).trans (hrel U s ⟨hU⟩)
    | zero => exact β.hom.map_zero
    | add a b _ _ ha hb => exact (β.hom.map_add a b).trans (by rw [ha, hb, add_zero])
    | smul r a _ ha => exact (β.hom.map_smul r a).trans (by rw [ha, smul_zero])
  have hh : ∀ (V : T.Opens) (m : Γ((Scheme.Modules.pullback ι).obj F, V)) (p : PLift (y ∈ V)),
      (h.val.app (op V)).hom m p = 0 := fun V m p =>
    (Stacks.ModuleSkyscraper.fromStalkLinear_germ (R := T.presheaf) h.val V p.down m).symm.trans
      (hβ _)
  have hq0 : ∀ m, q.hom m = 0 := by
    intro m
    obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
    exact (congrArg (fun k : F ⟶ (Scheme.Modules.pushforward ι).obj
      (Stacks.ModuleSkyscraper.skyModules T y A) => (k.val.app (op V)).hom s ⟨hV⟩) hgh).trans
        (hh _ _ _)
  have hall : ∀ m : M, (Submodule.Quotient.mk m : Q) ∈ (I • ⊤ : Submodule _ Q) := fun m =>
    (Submodule.Quotient.mk_eq_zero _).mp (hq0 m)
  have htop : (⊤ : Submodule (X.presheaf.stalk (ι y)) Q) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top ?_ ?_
    · rintro z -
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N z
      exact hall m
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
  rw [eq_top_iff]
  intro m _
  exact (Submodule.Quotient.mk_eq_zero N).mp ((Submodule.mem_bot _).mp
    (htop ▸ Submodule.mem_top : (Submodule.Quotient.mk m : Q) ∈ (⊥ : Submodule _ Q)))

/-- The section `φ⁻¹` of `𝒪_X(W)` over `U₀` given by a local equation `φ` of `W` on `U₀`. -/
private def localGenerator {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {W : Divisor X} {U₀ : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : W.IsLocalEquation U₀ φ) :
    W.divisorialSheaf.val.obj (op U₀) :=
  ⟨fun Z' => ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z'.1, fun P hP => by
    refine Or.inr ?_
    change WithZero.exp (-W.coeff P) ≤
      P.valuation (((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) P.component)
    rw [P.valuation_component, PrimeDivisor.ord_inv, hφ P hP]⟩

/-- A section of `𝒪_X(W)` over `V` times a local equation of `W` on `U₀` is a section of `𝒪_X`
over `V ⊓ U₀`. -/
private theorem isDivisorialSection_zero_mul_localEquation {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {W : Divisor X} {U₀ V : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : W.IsLocalEquation U₀ φ) (s : W.divisorialSubmodule V) :
    (0 : Divisor X).IsDivisorialSection (V ⊓ U₀) (fun Z =>
      s.1 ⟨Z.1, (inf_le_left : V ⊓ U₀ ≤ V) Z.2⟩ * (φ : RationalFunctions X) Z.1) := by
  intro E hE
  have h1 := s.2 E (hE.mono (Set.inter_subset_inter_right _ inf_le_left))
  have h2 : E.OrdGE (W.coeff E) ((φ : RationalFunctions X) E.component) := by
    refine Or.inr ?_
    rw [E.valuation_component, ← hφ E (hE.mono (Set.inter_subset_inter_right _ inf_le_right))]
  have h3 := h1.mul h2
  rw [neg_add_cancel] at h3
  simpa using h3

private theorem finite_stalk_divisorialSheaf {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {W : Divisor X} (hW : W.IsCartier) (x : X) :
    Module.Finite (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj W.divisorialSheaf) := by
  obtain ⟨U₀, hxU₀, φ, hφ⟩ := hW x
  let e := localGenerator hφ
  let ex : (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj W.divisorialSheaf :=
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) W.divisorialSheaf.val.presheaf U₀ x hxU₀).hom e
  refine ⟨⟨{ex}, ?_⟩⟩
  rw [eq_top_iff]
  rintro m -
  obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{0})
    W.divisorialSheaf.val.presheaf m
  set Ω : X.Opens := V ⊓ U₀ with hΩ
  have hxΩ : x ∈ Ω := ⟨hV, hxU₀⟩
  let s' : W.divisorialSubmodule V := s
  let ρfun : ToType ((rationalFunctionsPresheaf X).obj (op Ω)) := fun Z =>
    s'.1 ⟨Z.1, (inf_le_left : Ω ≤ V) Z.2⟩ * (φ : RationalFunctions X) Z.1
  have hρ : (0 : Divisor X).IsDivisorialSection Ω ρfun :=
    isDivisorialSection_zero_mul_localEquation hφ s'
  obtain ⟨ρ, hρeq⟩ := hρ.exists_eq
  have hsec : W.divisorialSheaf.presheaf.map (homOfLE inf_le_left : Ω ⟶ V).op s =
      ρ • W.divisorialSheaf.presheaf.map (homOfLE inf_le_right : Ω ⟶ U₀).op e := by
    refine Subtype.ext (funext fun Z => ?_)
    have hZ := congrFun hρeq Z
    rw [toRationalFunctionsPresheaf_app_apply] at hZ
    change s'.1 ⟨Z.1, _⟩ = X.presheaf.germ Ω _ Z.2 ρ *
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1
    rw [hZ]
    simp only [ρfun]
    rw [mul_assoc, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply,
      mul_one]
  have hgerm : (X.presheaf.germ Ω x hxΩ).hom ρ • ex =
      ((TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) W.divisorialSheaf.val.presheaf V x hV).hom s :
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj W.divisorialSheaf) := by
    rw [← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{0}) _
      (homOfLE inf_le_left : Ω ⟶ V) x hxΩ s]
    refine Eq.trans ?_ (congrArg _ hsec.symm)
    refine Eq.trans ?_ (Stacks.ModuleSkyscraper.germ_smul' (R := X.presheaf) W.divisorialSheaf.val
      x Ω hxΩ ρ _).symm
    exact congrArg _ (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{0})
      W.divisorialSheaf.val.presheaf (homOfLE inf_le_right : Ω ⟶ U₀) x hxΩ e).symm
  have hmem : (X.presheaf.germ Ω x hxΩ).hom ρ • ex ∈
      Submodule.span (X.presheaf.stalk x) {ex} :=
    Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  rw [hgerm] at hmem
  rw [Finset.coe_singleton]
  exact hmem

/-- **Spanning relative germs give a generating relative section.** If `D` is Cartier and the
germs at `x` of the sections of `𝒪_X(D)` over the opens `f⁻¹U` span the stalk, then some unit
`ψ` of `K(X)` has `D + div ψ` effective over some `f⁻¹U ∋ x` and zero along every prime divisor
through `x`: writing the local generator `φ⁻¹` as a combination of relative germs, one
coefficient times `sφ` is a unit of the local ring `𝒪_{X,x}`. -/
private theorem isGeneratedAt_of_span_relativeGerms {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Z) {D : Divisor X} (hD : D.IsCartier) (x : X)
    (hspan : Submodule.span (Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x)
      (relativeGerms f D.divisorialSheaf x) = ⊤) : IsGeneratedAt f D x := by
  classical
  obtain ⟨Zc, hxZc⟩ : ∃ Z' : irreducibleComponents X, x ∈ Z'.1 :=
    ⟨pointComponent x, mem_pointComponent x⟩
  obtain ⟨U₀, hxU₀, φ, hφ⟩ := hD x
  let e := localGenerator hφ
  have hmem : Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf U₀ hxU₀ e ∈
      Submodule.span (Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x)
        (relativeGerms f D.divisorialSheaf x) := hspan ▸ Submodule.mem_top
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  choose U hU s hs using fun i => (g i).2
  choose V hV c' hc' using
    fun i => TopCat.Presheaf.exists_germ_eq (C := RingCat.{0}) X.ringCatSheaf.obj (c i)
  let ev : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x D.divisorialSheaf →+
      X.presheaf.stalk (componentGenericPoint X Zc) :=
    AddMonoidHom.mk' (stalkValue D hxZc) (stalkValue_add D hxZc)
  have hval := congrArg ev hsum
  rw [map_sum] at hval
  have hterm : ∀ i, ev (c i • ↑(g i)) =
      X.presheaf.germ (V i) _ ((genericPoint_mem_iff Zc (V i)).mpr ⟨x, hV i, hxZc⟩) (c' i) *
        sectionValue D hxZc (hU i) (s i) := by
    intro i
    have h1 : c i • (↑(g i) : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x
        D.divisorialSheaf) =
        (TopCat.Presheaf.germ (C := RingCat.{0}) X.ringCatSheaf.obj (V i) x (hV i)).hom (c' i) •
          Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf _ (hU i) (s i) :=
      congrArg₂ (· • ·) (hc' i).symm (hs i).symm
    refine (congrArg ev h1).trans ?_
    refine (stalkValue_smul D hxZc (hV i) (c' i) _).trans ?_
    rw [stalkValue_modGerm]
  have he : ev (Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf U₀ hxU₀ e) =
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Zc :=
    stalkValue_modGerm D hxZc hxU₀ e
  rw [he] at hval
  simp only [hterm] at hval
  have hr : ∀ i, ∃ r : X.presheaf.stalk x, (stalkToRationalFunctions X hxZc).hom r =
      sectionValue D hxZc (hU i) (s i) * (φ : RationalFunctions X) Zc := by
    intro i
    exact (isDivisorialSection_zero_mul_localEquation hφ (s i : D.divisorialSubmodule _)
      ).exists_stalk_eq (x := x) ⟨hU i, hxU₀⟩ hxZc
  choose r hr using hr
  have hgerm : ∀ i, X.presheaf.germ (V i) _ ((genericPoint_mem_iff Zc (V i)).mpr
      ⟨x, hV i, hxZc⟩) (c' i) = (stalkToRationalFunctions X hxZc).hom
        (X.presheaf.germ (V i) x (hV i) (c' i)) :=
    fun i => (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  have hone : (stalkToRationalFunctions X hxZc).hom
      (∑ i, X.presheaf.germ (V i) x (hV i) (c' i) * r i) = 1 := by
    rw [map_sum]
    simp only [map_mul, hr, ← hgerm]
    have : ∑ i, X.presheaf.germ (V i) _ ((genericPoint_mem_iff Zc (V i)).mpr
        ⟨x, hV i, hxZc⟩) (c' i) * (sectionValue D hxZc (hU i) (s i) *
          (φ : RationalFunctions X) Zc) = (∑ i, X.presheaf.germ (V i) _
            ((genericPoint_mem_iff Zc (V i)).mpr ⟨x, hV i, hxZc⟩) (c' i) *
              sectionValue D hxZc (hU i) (s i)) * (φ : RationalFunctions X) Zc := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    rw [this, hval, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Pi.one_apply]
  have hone' : ∑ i, X.presheaf.germ (V i) x (hV i) (c' i) * r i = 1 :=
    stalkToRationalFunctions_injective hxZc (by rw [hone, map_one])
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hone' ▸ isUnit_one :
    IsUnit (∑ i ∈ Finset.univ, X.presheaf.germ (V i) x (hV i) (c' i) * r i))
  have hri : IsUnit (r i) := isUnit_of_mul_isUnit_right hi
  have := subsingleton_irreducibleComponents (X := X)
  let sR : RationalFunctions X := fun Z' => (s i : D.divisorialSubmodule _).1
    ⟨Z', (genericPoint_mem_iff Z' (f ⁻¹ᵁ U i)).mpr
      ⟨x, hU i, mem_irreducibleComponent_of_irreducibleSpace Z' x⟩⟩
  have hvali : sectionValue D hxZc (hU i) (s i) = (stalkToRationalFunctions X hxZc).hom (r i) *
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Zc := by
    rw [hr i, mul_assoc, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Pi.one_apply, mul_one]
  have hsR : IsUnit sR := by
    refine Pi.isUnit_iff.mpr fun Z' => ?_
    obtain rfl : Zc = Z' := Subsingleton.elim _ _
    change IsUnit (sectionValue D hxZc (hU i) (s i))
    rw [hvali]
    exact (hri.map _).mul ((φ⁻¹).isUnit.map (Pi.evalRingHom _ Zc))
  set ψ := hsR.unit
  have hψ : (ψ : RationalFunctions X) = sR := hsR.unit_spec
  have hgen : ∀ (Z' : irreducibleComponents X) (hx' : x ∈ Z'.1),
      (stalkToRationalFunctions X hx').hom (r i) =
        ((ψ * φ : (RationalFunctions X)ˣ) : RationalFunctions X) Z' := by
    intro Z' hx'
    obtain rfl : Zc = Z' := Subsingleton.elim _ _
    rw [Units.val_mul, Pi.mul_apply, hψ]
    exact hr i
  refine ⟨U i, hU i, ψ, fun P hP => ?_, fun P hxP => ?_⟩
  · have h1 := (s i : D.divisorialSubmodule _).2 P hP
    have hne : (ψ : RationalFunctions X) P.component ≠ 0 :=
      (ψ.isUnit.map (Pi.evalRingHom _ P.component)).ne_zero
    rw [hψ] at hne
    have h2 := h1.resolve_left hne
    change WithZero.exp (-D.coeff P) ≤ P.valuation (sR P.component) at h2
    rw [← hψ, P.valuation_component, WithZero.exp_le_exp] at h2
    linarith
  · have hspec : P.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
      exact specializes_iff_mem_closure.mpr hxP
    have hxPc : x ∈ P.component.1 := P.support_subset_component hxP
    have h0 : P.ord (ψ * φ) = 0 :=
      P.ord_eq_zero_of_isUnit (hri.map (X.presheaf.stalkSpecializes hspec).hom)
        (by rw [P.toComponent_stalkSpecializes hspec hxPc, hgen _ hxPc])
    rw [PrimeDivisor.ord_mul] at h0
    rw [hφ P ⟨x, hxP, hxU₀⟩]
    linarith

/-- An element of the stalk over `𝒪_{X,x}`, read in the stalk over the `RingCat`-valued
local ring: the two stalks have the same underlying group. -/
private abbrev toRingStalk {X : Scheme.{0}} {x : X} {F : X.Modules}
    (a : (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :
    Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x F := a

/-- The two scalar actions on the stalk of `F` agree on the germs of sections. -/
private theorem toRingStalk_germ_smul {X : Scheme.{0}} {x : X} (F : X.Modules) (U : X.Opens)
    (hx : x ∈ U) (r : Γ(X, U)) (s : F.val.obj (op U)) :
    toRingStalk ((X.presheaf.germ U x hx).hom r •
        (show (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F from
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F.val.presheaf U x hx).hom s)) =
      (TopCat.Presheaf.germ (C := RingCat.{0}) X.ringCatSheaf.obj U x hx).hom r •
        (show Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x F from
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F.val.presheaf U x hx).hom s) := by
  exact (Stacks.ModuleSkyscraper.germ_smul' (R := X.presheaf) F.val x U hx r s).symm.trans
    (AlgebraicGeometry.SheafOfModules.germ_hom_smul X.ringCatSheaf x F.val U hx r s)

/-- The span of the relative germs over the `CommRingCat`-valued local ring and over the
`RingCat`-valued one agree. -/
private theorem span_relativeGerms_eq_top_of_relSpan {X Z : Scheme.{0}} (f : X ⟶ Z)
    (F : X.Modules) (x : X) (h : relSpan f F x = ⊤) :
    Submodule.span (Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x) (relativeGerms f F x) = ⊤ := by
  have hsmul : ∀ (c : X.presheaf.stalk x)
      (a : (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F),
      ∃ c' : Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x,
        toRingStalk (c • a) = c' • toRingStalk a := by
    intro c a
    obtain ⟨V, hV, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf c
    obtain ⟨W, hW, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (C := AddCommGrpCat.{0}) F.val.presheaf a
    have hx : x ∈ V ⊓ W := ⟨hV, hW⟩
    refine ⟨(TopCat.Presheaf.germ (C := RingCat.{0}) X.ringCatSheaf.obj V x hV).hom r, ?_⟩
    rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
      ← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{0}) F.val.presheaf
        (homOfLE inf_le_right) x hx t,
      ← TopCat.Presheaf.germ_res_apply (C := RingCat.{0}) X.ringCatSheaf.obj
        (homOfLE inf_le_left) x hx r]
    exact toRingStalk_germ_smul F _ hx _ _
  suffices H : ∀ a : (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F, a ∈ relSpan f F x →
      toRingStalk a ∈ Submodule.span (Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x)
        (relativeGerms f F x) from
    eq_top_iff.mpr fun m _ => H m (h ▸ Submodule.mem_top)
  intro a ha
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨U, hU, s, rfl⟩ := hz
    exact Submodule.subset_span ⟨U, hU, s, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    obtain ⟨c', hc'⟩ := hsmul c a
    rw [hc']
    exact Submodule.smul_mem _ _ ha

end RelativeGerms

end MMP.SemiampleFloorUnionCriterion

end

namespace MMP.Fourfold

open MMP.Mori MMP.SemiampleFloorUnionCriterion Opposite

/-- **A semiample floor union gives semiampleness.** Let `(X, B)` be a `ℚ`-factorial dlt pair
with canonical divisor `K`, projective over a projective complex variety `Z` by `f`, and let
`T = ⌊B⌋`. Let `P ≥ 0` be `ℚ`-Cartier with `Supp P = Supp ⌊B⌋`, such that `K + B - εP` is
semiample over `Z` for all sufficiently small rational `ε > 0`. If some positive multiple
`m (K + B)` is a Cartier divisor `E` whose restriction `ι^* 𝒪_X(E)` to the reduced subscheme `T`
is generated over `Z`, then `K + B` is semiample over `Z`. -/
@[mmp "prop_fourfold_semiample_floor_union_criterion"]
public theorem QDivisor.isRelativelySemiample_of_isDltPair_of_restrict_roundDown
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (hfp : IsProjectiveMorphism f)
    {n : ℕ} (K : Divisor X) (B : QDivisor X) (hQ : IsQFactorial sX)
    (hdlt : MMP.Mori.IsDltPair sX n K B)
    (P : QDivisor X) (hP : P.IsEffective) (hPQ : P.IsQCartier) (hPT : P.supp = B.roundDown.supp)
    (hε : ∀ᶠ ε : ℚ in 𝓝[>] 0,
      QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B - ε • P))
    (hT : ∃ m : ℕ, 0 < m ∧ ∃ E : Divisor X,
      Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B) ∧ E.IsCartier ∧
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction
          (B.roundDown.suppIdeal.subschemeι ≫ f)).counit.app
        ((Scheme.Modules.pullback B.roundDown.suppIdeal.subschemeι).obj E.divisorialSheaf))) :
    QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) := by
  classical
  haveI := hZ
  set D : QDivisor X := Divisor.toQDivisor K + B with hD
  set ι := B.roundDown.suppIdeal.subschemeι with hι
  obtain ⟨ε₀, hε₀, hsemi⟩ : ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → ε < ε₀ →
      QDivisor.IsRelativelySemiample f (D - ε • P) := by
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hε
    exact ⟨u, hu, fun ε h1 h2 => hsub ⟨h1, h2⟩⟩
  set ε₁ : ℚ := ε₀ / 3 with hε₁
  set ε₂ : ℚ := 2 * ε₀ / 3 with hε₂
  obtain ⟨C₁, hC₁, m₁, hm₁, h₁, hfree₁⟩ := hsemi ε₁ (by positivity) (by linarith)
  obtain ⟨C₂, hC₂, -⟩ := hsemi ε₂ (by positivity) (by linarith)
  have hne : ε₂ - ε₁ ≠ 0 := by rw [hε₁, hε₂]; linarith
  set C : KCartierDivisor ℚ X := (ε₂ - ε₁)⁻¹ • (ε₂ • C₁ - ε₁ • C₂) with hCdef
  have hC : ∀ P', D.coeff P' = weilCoeff P' C := by
    intro P'
    have e1 := hC₁ P'
    have e2 := hC₂ P'
    rw [← weilCoeff_apply, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul] at e1 e2
    rw [hCdef, map_smul, map_sub, map_smul, map_smul, ← e1, ← e2, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  obtain ⟨m₀, hm₀, E₀, hE₀, hE₀C, hT₀⟩ := hT
  obtain ⟨d, hd, hdint⟩ := exists_pos_nsmul_intCast C
  set N : ℕ := 2 * m₀ * m₁ * d with hN
  have hNpos : 0 < N := by positivity
  have hNint : ∀ E, ∃ n : ℤ, ((N : ℚ) • C) E = n := by
    intro E
    obtain ⟨a, ha⟩ := hdint E
    refine ⟨(2 * m₀ * m₁ : ℕ) * a, ?_⟩
    rw [Finsupp.smul_apply] at ha ⊢
    rw [hN, smul_eq_mul] at *
    push_cast at ha ⊢
    rw [← ha]
    ring
  obtain ⟨W, hW, hWR⟩ := exists_isWeilDivisorOfCartier_realization ((N : ℚ) • C) hNint
    ((N : ℚ) • D) (fun P' => by
      simp only [DivisorWithCoeffs.coeff_smul, map_smul, hC, smul_eq_mul])
  refine isRelativelySemiample_of_isRelativelyFreeDivisor f D C hC hNpos hNint hWR ?_
  apply isRelativelyFreeDivisor_of_forall_exists
  intro x
  change IsGeneratedAt f W x
  by_cases hx : x ∈ B.roundDown.supp
  · obtain ⟨y, rfl⟩ : x ∈ Set.range ι := by
      rw [hι, Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.coe_support_suppIdeal]
      exact hx
    have hlift := epi_pushforward_map_unit_suppScheme_of_isRelativelySemiample sX sZ f hf hfp K B
      hdlt hQ P (DivisorWithCoeffs.isEffective_iff_nonneg.mp hP) hPQ hPT ⟨ε₀, hε₀, hsemi⟩
      (2 * m₀) (by omega) (E₀ + E₀)
      (by rw [map_add, hE₀, ← add_smul]; congr 1; push_cast; ring) (hE₀C.add hE₀C)
    have hspan := relSpan_eq_top_of_lift ι f _ y (ι.stalkMap_surjective y) hlift
      (relSpan_pullback_add_eq_top ι f hE₀C y (relSpan_eq_top_of_epi _ _ hT₀ y))
      (finite_stalk_divisorialSheaf (hE₀C.add hE₀C) _)
    have hg := isGeneratedAt_of_span_relativeGerms f (hE₀C.add hE₀C) _
      (span_relativeGerms_eq_top_of_relSpan f _ _ hspan)
    have hWe : W = ((m₁ * d : ℕ) : ℤ) • (E₀ + E₀) + 0 := by
      apply Divisor.toQDivisor_injective
      rw [hW, add_zero, map_zsmul, map_add, hE₀, ← add_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      congr 1
      rw [hN]
      push_cast
      ring
    rw [hWe]
    exact hg.nsmul_add _ (fun _ => le_rfl) (fun _ _ => rfl)
  · have hxP : x ∉ P.supp := hPT ▸ hx
    obtain ⟨w₁, hw₁, hw₁R⟩ := exists_isWeilDivisorOfCartier_realization ((m₁ : ℚ) • C₁) h₁
      ((m₁ : ℚ) • (D - ε₁ • P)) (fun P' => by
        simp only [DivisorWithCoeffs.coeff_smul, map_smul, smul_eq_mul, hC₁, weilCoeff_apply])
    have hg : IsGeneratedAt f w₁ x := exists_coeff_add_ord_eq_zero_of_isRelativelyFree f
      hw₁R.isCartier (isRelativelyFreeDivisor_of_isRelativelyFreeCartier f hw₁R hfree₁) x
    set k : ℕ := 2 * m₀ * d with hk
    set G : Divisor X := W - (k : ℤ) • w₁ with hG
    have hGq : ∀ Q, (G.coeff Q : ℚ) = N * ε₁ * P.coeff Q := by
      intro Q
      have a := congrArg (fun A : QDivisor X => A.coeff Q) hW
      have b := congrArg (fun A : QDivisor X => A.coeff Q) hw₁
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
        DivisorWithCoeffs.coeff_sub, smul_eq_mul] at a b
      rw [hG, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      push_cast
      rw [a, b, hN, hk]
      push_cast
      ring
    have hG0 : ∀ Q, 0 ≤ G.coeff Q := fun Q => by
      have : (0 : ℚ) ≤ G.coeff Q := by
        rw [hGq]
        exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (hP Q)
      exact_mod_cast this
    have hGx : ∀ Q : MMP.Mori.PrimeDivisor X, x ∈ Q.support → G.coeff Q = 0 := by
      intro Q hQx
      have hPQ0 : P.coeff Q = 0 := by
        by_contra hne
        exact hxP (DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, hne, hQx⟩)
      exact_mod_cast (show (G.coeff Q : ℚ) = 0 by rw [hGq, hPQ0, mul_zero])
    have hWe : W = (k : ℤ) • w₁ + G := by rw [hG]; abel
    rw [hWe]
    exact hg.nsmul_add k hG0 hGx

end MMP.Fourfold
