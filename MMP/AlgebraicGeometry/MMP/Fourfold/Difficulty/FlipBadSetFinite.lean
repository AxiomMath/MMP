module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.Echo
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.Singularities.TerminalThreefoldEchoCentres
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.MonomialValuationWeight
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Finiteness of the weighted bad set of a flip

For a small terminal flip move `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a prepared chain, written as a threefold
step diagram `Y⁻ → Z ← Y⁺` with both maps small and bad loci `W^±`, the weighted bad set `𝒜₀` of
normalized divisorial valuations `v` exceptional over both `Y⁻` and `Y⁺`, with `c_{Y⁻}(v) ⊆ W⁻`
and `w_v(Y⁻, Θ⁻) + w_v(Y⁺, Θ⁺) > 0`, is finite.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.finite_flipBadSet`: the weighted bad set
  `MMP.Fourfold.StabilizedTail.PreparedChain.flipBadSet` of a flip move is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

universe u

namespace MMP.IndexdFlipBadSetFinite

/-- Dimension arithmetic: `d + 2 = 3` forces `d = 1`. -/
private theorem eq_one_of_add_two_eq_three {d : WithBot ℕ∞}
    (h : d + ((2 : ℕ∞) : WithBot ℕ∞) = 3) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe e =>
      have h' : (((e + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((3 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast; exact h
      have : e + 2 = 3 := by exact_mod_cast WithBot.coe_injective h'
      obtain rfl : e = 1 := by omega
      rfl

/-- Pulling valuations back along a surjective ring homomorphism is injective. -/
private theorem comap_injective_of_surjective {R S : Type*} [Ring R] [Ring S]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {f : R →+* S}
    (hf : Function.Surjective f) :
    Function.Injective fun ξ : Valuation S Γ₀ => ξ.comap f := by
  intro ξ ξ' h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congrArg (fun ν : Valuation R Γ₀ => ν y) h

/-! ### Closed sets of a threefold without divisors -/

section BadLoci

open MMP.Mori MMP.Fourfold

/-- Coheight arithmetic: `2 ≤ a`, `a + 1 ≤ b ≤ 3` force `a = 2`. -/
private theorem eq_two_of_add_one_le {a b : ℕ∞} (ha : 2 ≤ a) (hab : a + 1 ≤ b) (hb : b ≤ 3) :
    a = 2 := by
  induction b using ENat.recTopCoe with
  | top => exact absurd hb (by decide)
  | coe b =>
    induction a using ENat.recTopCoe with
    | top => exact absurd hab (by simp)
    | coe a => norm_cast at ha hab hb ⊢; omega

/-- On a scheme of dimension three every point has coheight at most three. -/
private theorem coheight_le_three {X : Scheme.{0}} (hdim : topologicalKrullDim X = 3) (x : X) :
    Order.coheight x ≤ 3 := by
  have e4 := Order.coheight_le_krullDim x
  have hX : Order.krullDim X = 3 := by
    rw [← hdim, topologicalKrullDim,
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  rw [hX] at e4
  exact WithBot.coe_le_coe.mp
    (e4 : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) ≤ ((3 : ℕ∞) : WithBot ℕ∞))

/-- In an integral scheme, a set avoiding the generic point and the generic points of all prime
divisors consists of points of coheight at least two. -/
private theorem two_le_coheight_of_mem {X : Scheme.{0}} [IsIntegral X] {W : Set X}
    (hη : genericPoint X ∉ W) (hP : ∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∉ W)
    {x : X} (hx : x ∈ W) : 2 ≤ Order.coheight x := by
  have h0 : Order.coheight x ≠ 0 := by
    intro h
    rw [Order.coheight_eq_zero] at h
    have hle : genericPoint X ≤ x := h (genericPoint_specializes x)
    exact hη (((genericPoint_specializes x).antisymm hle).eq ▸ hx)
  have h1 : Order.coheight x ≠ 1 := fun h => hP (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h)
    (by
      show AlgebraicGeometry.PrimeDivisor.genericPoint _ ∈ W
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      exact hx)
  generalize Order.coheight x = c at h0 h1 ⊢
  induction c using ENat.recTopCoe with
  | top => exact le_top
  | coe c => norm_cast at h0 h1 ⊢; omega

/-- Let `X` be an integral scheme of dimension three, of finite type over `ℂ`, and `W ⊆ X` a closed
set all of whose points have coheight at least two. Then every irreducible closed subset of `W`
is a point or one of finitely many curves (the irreducible components of `W`). -/
private theorem exists_finite_of_two_le_coheight {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] [NoetherianSpace X]
    (hdim : topologicalKrullDim X = 3) (W : Closeds X)
    (hW : ∀ x ∈ (W : Set X), 2 ≤ Order.coheight x) :
    ∃ F : Set (IrreducibleCloseds X), F.Finite ∧ ∀ Z : IrreducibleCloseds X, (Z : Set X) ⊆ W →
      (∃ y, (Z : Set X) = {y}) ∨ (Z ∈ F ∧ topologicalKrullDim (Z : Set X) = 1) := by
  classical
  obtain ⟨S, hSirr, hSW⟩ := NoetherianSpace.exists_finset_irreducible W
  refine ⟨{Z | (Z : Set X) ∈ (S.image (fun C : Closeds X => (C : Set X)) : Set (Set X))},
    (Finset.finite_toSet _).preimage SetLike.coe_injective.injOn, fun Z hZW => ?_⟩
  have hgen : IsGenericPoint Z.isIrreducible.genericPoint (Z : Set X) :=
    Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed
  set η := Z.isIrreducible.genericPoint
  have hη : η ∈ (Z : Set X) := hgen.mem
  have h2 : 2 ≤ Order.coheight η := hW η (hZW hη)
  by_cases hs : ∀ c ∈ (Z : Set X), c = η
  · exact Or.inl ⟨η, Set.eq_singleton_iff_unique_mem.2 ⟨hη, hs⟩⟩
  push Not at hs
  obtain ⟨c, hc, hcη⟩ := hs
  have hη2 : Order.coheight η = 2 := eq_two_of_add_one_le h2
    (MMP.Flips.coheight_add_one_le_of_specializes (hgen.specializes hc) (Ne.symm hcη))
    (coheight_le_three hdim c)
  refine Or.inr ⟨?_, ?_⟩
  · have hsub : (Z : Set X) ⊆
        ⋃₀ ((S.image (fun C : Closeds X => (C : Set X)) : Finset (Set X)) : Set (Set X)) := by
      intro x hx
      obtain ⟨C, hC, hxC⟩ : ∃ C ∈ S, x ∈ (C : Set X) := by
        simpa [hSW, Closeds.coe_finset_sup] using hZW hx
      exact ⟨C, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hC), hxC⟩
    obtain ⟨C', hC', hZC⟩ := (isIrreducible_iff_sUnion_isClosed.mp Z.isIrreducible) _
      (fun z hz => by
        obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hz
        exact C.isClosed) hsub
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hC'
    have hCirr : IsIrreducible (C : Set X) := hSirr ⟨C, hC⟩
    have hCW : (C : Set X) ⊆ W := by
      rw [hSW]
      exact Finset.le_sup (f := id) hC
    have hgenC : IsGenericPoint hCirr.genericPoint (C : Set X) :=
      hCirr.isGenericPoint_genericPoint C.isClosed
    have hηC : hCirr.genericPoint = η := by
      by_contra hne
      have h3 := MMP.Flips.coheight_add_one_le_of_specializes (hgenC.specializes (hZC hη)) hne
      have h4 : 2 ≤ Order.coheight hCirr.genericPoint := hW _ (hCW hgenC.mem)
      rw [hη2] at h3
      have : (2 : ℕ∞) + 1 ≤ 2 := (add_le_add h4 le_rfl).trans h3
      exact absurd this (by decide)
    have hZC' : (Z : Set X) = C := by
      rw [← hgen.def, ← hgenC.def, hηC]
    change (Z : Set X) ∈ (S.image (fun C : Closeds X => (C : Set X)) : Set (Set X))
    rw [hZC']
    exact Finset.mem_coe.mpr hC'
  · have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX η
    rw [hgen.def, hη2, hdim] at h
    exact eq_one_of_add_two_eq_three h

end BadLoci

/-! ### Proper birational morphisms over points of codimension one -/

section Biregular

open MMP.Mori MMP.Fourfold

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over every point
with finite fibre. -/
private theorem mem_biregularLocus_of_finite {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsNormal Z] (f : X ⟶ Z) [IsProper f] (hb : IsBirationalMorphism f) {z : Z}
    (hz : (f ⁻¹' {z}).Finite) : z ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).1 inferInstance
  exact le_biregularLocus (V := ⟨_, hU⟩) hiso hz

/-- A proper birational morphism onto a normal variety is an isomorphism over every point of
codimension one. -/
private theorem mem_biregularLocus_of_coheight_eq_one {X Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral X] (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hb : IsBirationalMorphism f) {z : Z} (hz : Order.coheight z = 1) : z ∈ biregularLocus f := by
  haveI := hZ.1.toIsIntegral
  haveI := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  rw [← AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hz]
  exact Oai4C1.genericPoint_mem_biregularLocus f hb _

/-- The generic point of the target lies in the biregular locus of a proper birational
morphism of varieties onto a normal variety. -/
private theorem genericPoint_mem_biregularLocus {X Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hb : IsBirationalMorphism f) :
    haveI := hZ.1.toIsIntegral
    genericPoint Z ∈ biregularLocus f := by
  haveI := hZ.1.toIsIntegral
  haveI := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hb.isDominant
  have hfin := MMP.Mori.map_genericPoint_mem_finiteFibreLocus f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
  rw [MMP.Positivity.map_genericPoint_eq_of_isDominant] at hfin
  exact mem_biregularLocus_of_finite f hb hfin

/-- If the exceptional set of `f` has codimension at least two, then `f` and every proper
birational `g` onto the same normal variety are isomorphisms over the image of the generic point
of a prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {X Y Z : Scheme.{0}} [IsIntegral Y]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z)
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f))
    (g : Y ⟶ Z) [IsProper g] (hb : IsBirationalMorphism g)
    (P : AlgebraicGeometry.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f ∧ f P.genericPoint ∈ biregularLocus g := by
  have h1 := Oai4C1.map_genericPoint_mem_biregularLocus h2 P
  refine ⟨h1, mem_biregularLocus_of_coheight_eq_one hZ g hb ?_⟩
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f h1,
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]

/-- Precomposing with an isomorphism does not shrink the biregular locus. -/
private theorem biregularLocus_le_biregularLocus_comp {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus f ≤ biregularLocus (φ ≫ f) :=
  sSup_le fun V hV => le_biregularLocus (by
    have : IsIso (f ∣_ V) := hV
    change IsIso ((φ ≫ f) ∣_ V)
    rw [morphismRestrict_comp]
    have h2 : IsIso (φ ∣_ (f ⁻¹ᵁ V)) := by infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 this)

/-- Precomposing with an isomorphism does not change the biregular locus. -/
private theorem biregularLocus_comp_of_isIso {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus (φ ≫ f) = biregularLocus f := by
  refine le_antisymm ?_ (biregularLocus_le_biregularLocus_comp φ f)
  have := biregularLocus_le_biregularLocus_comp (inv φ) (φ ≫ f)
  rwa [IsIso.inv_hom_id_assoc] at this

end Biregular

/-! ### Divisors over a variety seen over a birational model -/

section CompProper

open MMP.Mori MMP.Fourfold

variable {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- A divisor `(W, h, E)` over `X`, with `h` proper, seen over `X'` through a proper birational
morphism `g : X ⟶ X'` over `ℂ`: the divisor `(W, g ∘ h, E)`. -/
private noncomputable def compProper {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) : DivisorOver ℂ sX' where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    rw [Category.assoc, hs]
    exact D.isNormalVariety
  isBirationalMorphism := by
    haveI := D.isIntegral
    haveI := hD
    exact isBirationalMorphism_comp_of_isBirational g D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

/-- The divisor `(W, g ∘ h, E)` has the valuation `ord_E` read on `k(X')` through `g`. -/
private theorem valuation_compProper {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) :
    haveI := hg.isDominant
    (compProper g hg hs D hD).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := hg.isDominant
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

end CompProper

/-! ### Finiteness for a pair of small morphisms -/

section Finiteness

open MMP.Mori MMP.Fourfold

/-- Let `f^± : X^± ⟶ Z` be proper birational morphisms over `ℂ` onto a normal variety, isomorphisms
over the images of the generic points of all prime divisors, and let `(X^±, Θ^±)` be terminal
pairs on projective `ℚ`-factorial threefolds. Then the normalized divisorial valuations `v` of
`ℂ(X⁻)` with centre in the bad locus `W⁻` and with `a(v; X⁻, Θ⁻) < 2`, or with corresponding
valuation `v⁺` of `ℂ(X⁺)` exceptional over `X⁺` and `a(v⁺; X⁺, Θ⁺) < 2`, form a finite set. -/
private theorem finite_setOf_isCentre_subset_badLocusMinus {Xm Xp Z : Scheme.{0}}
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
    (hZ : IsNormalVariety ℂ sZ) {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsProper fm] [IsProper fp]
    (hbm : IsBirationalMorphism fm) (hbp : IsBirationalMorphism fp) (hm : fm ≫ sZ = sXm)
    (hp : fp ≫ sZ = sXp)
    (hPm : ∀ P : AlgebraicGeometry.PrimeDivisor Xm,
      fm P.genericPoint ∈ commonBiregularLocus fm fp)
    (hPp : ∀ P : AlgebraicGeometry.PrimeDivisor Xp,
      fp P.genericPoint ∈ commonBiregularLocus fm fp)
    (hYm : MMP.Mori.IsProjectiveVariety ℂ sXm) (hQm : IsQFactorial sXm)
    (hdm : topologicalKrullDim Xm = 3) {Θm : QDivisor Xm} (hΘm : IsKltTerminalPair sXm Θm)
    (hYp : MMP.Mori.IsProjectiveVariety ℂ sXp) (hQp : IsQFactorial sXp)
    (hdp : topologicalKrullDim Xp = 3) {Θp : QDivisor Xp} (hΘp : IsKltTerminalPair sXp Θp) :
    haveI := hbm.isDominant
    haveI := hbp.isDominant
    {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ)) |
      (∃ Zc : IrreducibleCloseds Xm, MMP.Intersection.IsCentre ℂ sXm v Zc ∧
          (Zc : Set Xm) ⊆ badLocusMinus fm fp) ∧
        ∃ v' : Valuation Xp.functionField (WithZero (Multiplicative ℤ)),
          v'.comap (functionFieldMap fp) = v.comap (functionFieldMap fm) ∧
          ((∃ a < 2, HasLogDiscrepancy sXm Θm v a) ∨
            (MMP.Intersection.IsExceptionalValuation ℂ sXp v' ∧
              ∃ a < 2, HasLogDiscrepancy sXp Θp v' a))}.Finite := by
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hXm := hΘm.1.1.isPair.1
  have hXp := hΘp.1.1.isPair.1
  haveI : LocallyOfFiniteType sXm := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sXp := hXp.1.toLocallyOfFiniteType
  haveI : QuasiCompact sXm := hXm.1.toQuasiCompact
  haveI : QuasiCompact sXp := hXp.1.toQuasiCompact
  haveI : CompactSpace Xm := QuasiCompact.compactSpace_of_compactSpace sXm
  haveI : CompactSpace Xp := QuasiCompact.compactSpace_of_compactSpace sXp
  haveI : IsNoetherian Xm := {}
  haveI : IsNoetherian Xp := {}
  have hηZ : genericPoint Z ∈ commonBiregularLocus fm fp :=
    ⟨genericPoint_mem_biregularLocus hZ fm hbm, genericPoint_mem_biregularLocus hZ fp hbp⟩
  have hηm : genericPoint Xm ∉ (badLocusMinus fm fp : Set Xm) := fun hη =>
    hη (show fm (genericPoint Xm) ∈ commonBiregularLocus fm fp from
      MMP.Positivity.map_genericPoint_eq_of_isDominant fm ▸ hηZ)
  have hηp : genericPoint Xp ∉ (badLocusPlus fm fp : Set Xp) := fun hη =>
    hη (show fp (genericPoint Xp) ∈ commonBiregularLocus fm fp from
      MMP.Positivity.map_genericPoint_eq_of_isDominant fp ▸ hηZ)
  obtain ⟨Fm, hFm, hcm⟩ := exists_finite_of_two_le_coheight sXm hdm (badLocusMinus fm fp)
    fun x hx => two_le_coheight_of_mem hηm (fun P hP => hP (hPm P)) hx
  obtain ⟨Fp, hFp, hcp⟩ := exists_finite_of_two_le_coheight sXp hdp (badLocusPlus fm fp)
    fun x hx => two_le_coheight_of_mem hηp (fun P hP => hP (hPp P)) hx
  have hAm := finite_setOf_isCentre_singleton sXm hYm hQm hdm hΘm (L := Θm.support) subset_rfl
  have hBm := (hFm.inter_of_left {V | topologicalKrullDim (V : Set Xm) = 1}).biUnion
    fun V hV => finite_setOf_isCentre sXm hYm hQm hdm hΘm (L := Θm.support) subset_rfl V hV.2
  have hAp := finite_setOf_isCentre_singleton sXp hYp hQp hdp hΘp (L := Θp.support) subset_rfl
  have hBp := (hFp.inter_of_left {V | topologicalKrullDim (V : Set Xp) = 1}).biUnion
    fun V hV => finite_setOf_isCentre sXp hYp hQp hdp hΘp (L := Θp.support) subset_rfl V hV.2
  have hinj := comap_injective_of_surjective (Γ₀ := ℤᵐ⁰) hbm.functionFieldMap_bijective.2
  refine ((hAm.union hBm).union (((hAp.union hBp).image
    fun v' => v'.comap (functionFieldMap fp)).preimage hinj.injOn)).subset ?_
  rintro v ⟨⟨Zc, hZc, hZW⟩, v', hv', h | ⟨hexc, h⟩⟩
  · rcases hcm Zc hZW with ⟨y, hy⟩ | ⟨hZF, hZ1⟩
    · exact Or.inl (Or.inl ⟨⟨Zc, y, hZc, hy⟩, h⟩)
    · exact Or.inl (Or.inr (Set.mem_biUnion (x := Zc) ⟨hZF, hZ1⟩ ⟨hZc, h⟩))
  · obtain ⟨D', hD'p, hv'D', -⟩ := hexc
    obtain ⟨D, hDp, hvD, hZD⟩ := hZc
    have hZ'c : MMP.Intersection.IsCentre ℂ sXp v' D'.center := ⟨D', hD'p, hv'D', rfl⟩
    have hZ'W : (D'.center : Set Xp) ⊆ badLocusPlus fm fp := by
      have hmem : D.f D.E.genericPoint ∈ (badLocusMinus fm fp : Set Xm) := hZW (by
        rw [hZD, D.center_eq_closure_genericPoint]
        exact subset_closure rfl)
      have heq := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hZ
        (D := compProper fp hbp hp D' hD'p) (D' := compProper fm hbm hm D hDp) (by
          rw [valuation_compProper, valuation_compProper, ← hv'D', ← hvD, hv'])
      rw [D'.center_eq_closure_genericPoint]
      refine (badLocusPlus fm fp).isClosed.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr fun hU => hmem ?_)
      change fp (D'.f D'.E.genericPoint) = fm (D.f D.E.genericPoint) at heq
      change fm (D.f D.E.genericPoint) ∈ commonBiregularLocus fm fp
      rw [← heq]
      exact hU
    refine Or.inr ⟨v', ?_, hv'⟩
    rcases hcp _ hZ'W with ⟨y, hy⟩ | ⟨hZF, hZ1⟩
    · exact Or.inl ⟨⟨_, y, hZ'c, hy⟩, h⟩
    · exact Or.inr (Set.mem_biUnion (x := D'.center) ⟨hZF, hZ1⟩ ⟨hZ'c, h⟩)

end Finiteness

/-! ### The flip moves of a prepared chain -/

section Chain

open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedTail

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a programme
is compatible with the morphisms `π_a`, `π_b` to the base. -/
private theorem eqToHom_comp_modelMap {V Z : Scheme.{0}} {Y : ℕ → Scheme.{0}} (π : V ⟶ Z)
    (πY : ∀ k, Y k ⟶ Z) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V Y) h) ≫ modelMap π πY b = modelMap π πY a := by
  subst h; simp

/-- The morphism `V_{k+1} ⟶ T_k` of the `k`-th flip of the `i`-th bridge of a terminal chain is
proper and birational, lies over `ℂ`, and is an isomorphism over the image of the generic point of
every prime divisor, as is `g_k : V_k ⟶ T_k`. -/
private theorem flipTargetMapOf_properties {T : StabilizedTail} (C : TerminalChain T) (i : ℕ)
    (k : Fin (C.bridge i).P.m) (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) :
    IsProper (C.flipTargetMapOf i k d) ∧ IsBirationalMorphism (C.flipTargetMapOf i k d) ∧
      C.flipTargetMapOf i k d ≫ (C.bridge i).P.sT k = C.modelStructure (C.flipTargetOf i k d) ∧
      ∀ P : AlgebraicGeometry.PrimeDivisor (C.model (C.flipTargetOf i k d)),
        C.flipTargetMapOf i k d P.genericPoint ∈
          commonBiregularLocus ((C.bridge i).P.g k) (C.flipTargetMapOf i k d) := by
  have hD := (C.bridge i).P.isThreefoldStepDiagram k k.2
  have hZ := hD.isNormalVariety_target
  haveI := C.isIntegral_flipBase i k
  haveI : IsNormal ((C.bridge i).P.T k) := hZ.2
  haveI : LocallyOfFiniteType ((C.bridge i).P.sT k) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian ((C.bridge i).P.T k) :=
    LocallyOfFiniteType.isLocallyNoetherian ((C.bridge i).P.sT k)
  haveI : IsProper ((C.bridge i).P.g k) :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper ((C.bridge i).P.gp k) := hD.isSmallMorphism_plus.isProper
  have hsp := hD.isSmallMorphism_plus
  have key : ∀ x : (C.bridge i).P.Y k, Order.coheight x = 1 →
      (C.bridge i).P.gp k x ∈ commonBiregularLocus ((C.bridge i).P.g k) ((C.bridge i).P.gp k) :=
    fun x hx => by
      have h := map_genericPoint_mem_biregularLocus hZ ((C.bridge i).P.gp k)
        hsp.two_le_codimension ((C.bridge i).P.g k) hD.isBirationalMorphism_minus
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx)
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at h
      exact ⟨h.2, h.1⟩
  cases d with
  | isTrue h =>
    exact ⟨hsp.isProper, hsp.isBirationalMorphism, hD.comp_eq_plus, fun P =>
      key _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)⟩
  | isFalse h =>
    have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
    let ψ : (C.junction (i + 1)).Y ≅ (C.bridge i).P.Y k := (C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)
    change IsProper (ψ.hom ≫ (C.bridge i).P.gp k) ∧
      IsBirationalMorphism (ψ.hom ≫ (C.bridge i).P.gp k) ∧
      (ψ.hom ≫ (C.bridge i).P.gp k) ≫ (C.bridge i).P.sT k =
        (C.junction (i + 1)).p ≫ T.sX (i + 1) ∧
      ∀ P : AlgebraicGeometry.PrimeDivisor (C.junction (i + 1)).Y,
        (ψ.hom ≫ (C.bridge i).P.gp k) P.genericPoint ∈
          commonBiregularLocus ((C.bridge i).P.g k) (ψ.hom ≫ (C.bridge i).P.gp k)
    refine ⟨inferInstance, ?_, ?_, fun P => ?_⟩
    · exact isBirationalMorphism_comp_of_isBirational _ _
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hsp.isBirationalMorphism)
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          (isBirationalMorphism_of_isIso ψ.hom))
    · rw [Category.assoc, ← (C.bridge i).P.comp_eq_base k k.2,
        ← Category.assoc _ _ (T.sZ i), ← (C.bridge i).P.πY_eq k k.2]
      change ((C.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)) ≫
        modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY (k.1 + 1) ≫ T.sZ i = _
      rw [Category.assoc, ← Category.assoc (eqToHom _), eqToHom_comp_modelMap _ _ hmk,
        (C.bridge i).modelMap_eq]
      simp [(T.isThreefoldStepDiagram i).comp_eq_plus]
    · have hx : ψ.hom P.genericPoint ∈ biregularLocus ψ.hom :=
        le_biregularLocus (V := ⊤) (inferInstance : IsIso (ψ.hom ∣_ ⊤)) trivial
      have h1 := key (ψ.hom P.genericPoint) (by
        rw [MMP.Positivity.coheight_map_of_mem_biregularLocus ψ.hom hx,
          AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
      change (C.bridge i).P.gp k (ψ.hom P.genericPoint) ∈ biregularLocus ((C.bridge i).P.g k) ⊓
        biregularLocus (ψ.hom ≫ (C.bridge i).P.gp k)
      rw [biregularLocus_comp_of_isIso]
      exact h1

end Chain

end MMP.IndexdFlipBadSetFinite

namespace MMP.Fourfold.StabilizedTail.PreparedChain

open MMP.Mori MMP.IndexdFlipBadSetFinite in
/-- The weighted bad set `𝒜₀` of a small terminal flip move of a prepared chain is finite. -/
@[mmp "lem_mmp_indexd_flip_bad_set_finite"]
public theorem finite_flipBadSet {T : StabilizedTail} (Q : PreparedChain T) (μ : Q.FlipMove) :
    (Q.flipBadSet μ).Finite := by
  have hD := (Q.chain.bridge μ.1.1).P.isThreefoldStepDiagram μ.1.2 μ.1.2.2
  have : IsProper ((Q.chain.bridge μ.1.1).P.g μ.1.2) :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  have : IsProper μ.sourceMap :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  obtain ⟨hpp, hbp, hp, hPp⟩ :=
    flipTargetMapOf_properties Q.chain μ.1.1 μ.1.2 inferInstance
  have : IsProper μ.targetMap := hpp
  have hPm : ∀ P : AlgebraicGeometry.PrimeDivisor (Q.chain.model μ.source.1),
      μ.sourceMap P.genericPoint ∈ MMP.Fourfold.commonBiregularLocus μ.sourceMap μ.targetMap :=
    fun P => map_genericPoint_mem_biregularLocus hD.isNormalVariety_target μ.sourceMap
      ((Q.chain.bridge μ.1.1).isSmallMorphism μ.1.2 μ.1.2.2).two_le_codimension μ.targetMap hbp P
  obtain ⟨hΘm, hYm, hQm, hdm, -⟩ := Q.echoSetting_model μ.source
  obtain ⟨hΘp, hYp, hQp, hdp, -⟩ := Q.echoSetting_model μ.target
  refine (finite_setOf_isCentre_subset_badLocusMinus hD.isNormalVariety_target
    hD.isBirationalMorphism_minus hbp hD.comp_eq_minus hp hPm hPp hYm hQm hdm hΘm hYp hQp hdp
    hΘp).subset ?_
  have hlt : ∀ {a : ℝ} {w : ℕ}, 0 < w → w = MMP.Fourfold.difficultyWeight Q.scale (2 - a) →
      a < 2 := fun hw hwa => lt_of_not_ge fun ha =>
    hw.ne' (hwa.trans (MMP.Fourfold.difficultyWeight_of_nonpos (sub_nonpos.2 ha)))
  rintro v ⟨hc, v', hv', w, w', hw, hw', hpos⟩
  refine ⟨hc, v', hv', ?_⟩
  rcases Nat.eq_zero_or_pos w with hw0 | hw0
  · obtain ⟨hexc, a, ⟨n, D, -, hDv, hl⟩, hwa⟩ := hw'
    exact Or.inr ⟨hexc, a, hlt (by omega) hwa, n, D, hDv, hl⟩
  · obtain ⟨-, a, ⟨n, D, -, hDv, hl⟩, hwa⟩ := hw
    exact Or.inl ⟨a, hlt hw0 hwa, n, D, hDv, hl⟩

end MMP.Fourfold.StabilizedTail.PreparedChain
