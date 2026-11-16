module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair

/-!
# The weighted bad set of a flip is finite

For a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a bridge of a prepared chain, the weighted
bad set `𝒜₀` (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.flipBadSet`) is finite.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.finite_flipBadSet`: `𝒜₀` is finite.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_lem_oai4_c3_flip_bad_set_finite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

/-! ### Closed sets of a fourfold without divisors -/

/-- Dimension arithmetic: `d + 2 = 4` forces `d = 2`. -/
private theorem eq_two_of_add_two_eq_four {d : WithBot ℕ∞}
    (h : d + ((2 : ℕ∞) : WithBot ℕ∞) = 4) : d = 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe e =>
      have h' : (((e + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast; exact h
      have : e + 2 = 4 := by exact_mod_cast WithBot.coe_injective h'
      obtain rfl : e = 2 := by omega
      rfl

/-- A strict specialization raises the coheight. -/
private theorem coheight_add_one_le_of_specializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (hne : x ≠ y) : Order.coheight x + 1 ≤ Order.coheight y :=
  Order.coheight_add_one_le (lt_of_le_not_ge h fun e => hne (h.antisymm e).eq)

/-- Let `X` be an integral scheme of dimension four, of finite type over `ℂ`, and `W ⊆ X` a closed
set all of whose points have coheight at least two. Then every irreducible closed subset of `W`
has codimension at least three or is one of finitely many surfaces (the surface components of
`W`). -/
private theorem exists_finite_of_two_le_coheight {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] [NoetherianSpace X]
    (hdim : topologicalKrullDim X = 4) (W : Closeds X)
    (hW : ∀ x ∈ (W : Set X), 2 ≤ Order.coheight x) :
    ∃ F : Set (IrreducibleCloseds X), F.Finite ∧ ∀ Z : IrreducibleCloseds X, (Z : Set X) ⊆ W →
      3 ≤ codimension Z ∨ (Z ∈ F ∧ topologicalKrullDim (Z : Set X) = 2) := by
  classical
  obtain ⟨S, hSirr, hSW⟩ := NoetherianSpace.exists_finset_irreducible W
  refine ⟨{Z | (Z : Set X) ∈ (S.image (fun C : Closeds X => (C : Set X)) : Set (Set X))},
    (Finset.finite_toSet _).preimage SetLike.coe_injective.injOn, fun Z hZW => ?_⟩
  have hgen := Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed
  set η := Z.isIrreducible.genericPoint
  have hη : η ∈ (Z : Set X) := hgen.mem
  have h2 : 2 ≤ Order.coheight η := hW η (hZW hη)
  have hcod : codimension Z = Order.coheight η := by
    have hEq : (irreducibleSetEquivPoints (α := X)).symm η = Z := IrreducibleCloseds.ext hgen.def
    rw [codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  by_cases h3 : 3 ≤ Order.coheight η
  · exact Or.inl (hcod ▸ h3)
  have hη2 : Order.coheight η = 2 :=
    le_antisymm ((ENat.lt_add_one_iff (by simp)).mp (not_le.mp h3)) h2
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
    have hgenC := hCirr.isGenericPoint_genericPoint C.isClosed
    have hηC : hCirr.genericPoint = η := by
      by_contra hne
      have h3 := coheight_add_one_le_of_specializes (hgenC.specializes (hZC hη)) hne
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
    exact eq_two_of_add_two_eq_four h

/-! ### The bad loci of a pair of small morphisms -/

section BadLocus

/-- Precomposing with an isomorphism does not shrink the biregular locus. -/
private theorem biregularLocus_le_biregularLocus_comp {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus f ≤ biregularLocus (φ ≫ f) :=
  sSup_le fun V hV => le_biregularLocus (by
    have : IsIso (f ∣_ V) := hV
    change IsIso ((φ ≫ f) ∣_ V)
    rw [morphismRestrict_comp]
    have h2 : IsIso (φ ∣_ (f ⁻¹ᵁ V)) := by infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 this)

/-- A small morphism onto a normal scheme is an isomorphism over the points of codimension at
most one: every point outside its biregular locus has coheight at least two. -/
private theorem two_le_coheight_of_notMem_biregularLocus {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {g : X ⟶ Z} (hg : IsSmallMorphism sX sZ g) {z : Z}
    (hz : z ∉ biregularLocus g) : 2 ≤ Order.coheight z := by
  haveI := hg.isProper
  haveI := hg.isBirationalMorphism.isDominant
  by_contra h
  exact hz (MMP.Positivity.mem_biregularLocus_of_coheight_le_one g
    hg.isBirationalMorphism.functionFieldMap_bijective hg.two_le_codimension
    (Order.le_of_lt_add_one (not_le.mp h)))

/-- A point `y` of `A` mapping into a set of points of coheight at least two under `φ ≫ g`, with
`φ` an isomorphism and `g` of exceptional set of codimension at least two, has coheight at least
two. -/
private theorem two_le_coheight_of_comp_mem {A X Z : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (g : X ⟶ Z) (hg : 2 ≤ closedsCodimension (exceptionalSet g)) {T : Set Z}
    (hT : ∀ z ∈ T, 2 ≤ Order.coheight z) {y : A} (hy : (φ ≫ g) y ∈ T) :
    2 ≤ Order.coheight y := by
  rw [← Topology.IsOpenEmbedding.coheight_eq _ φ.isOpenEmbedding]
  by_cases hb : g (φ y) ∈ biregularLocus g
  · rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g hb]
    exact hT _ hy
  · exact MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hg (mem_exceptionalSet.mpr hb)

/-- For small morphisms `f⁻ : X⁻ ⟶ Z` and `g : X⁺ ⟶ Z` onto a normal scheme and `f⁺ = φ ≫ g`
with `φ` an isomorphism, every point of `Σ = Z ∖ U` has coheight at least two. -/
private theorem two_le_coheight_of_mem_badLocusBase {Xm Xp A Z : Scheme.{0}} [IsIntegral Xm]
    [IsIntegral Xp] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {fm : Xm ⟶ Z}
    {g : Xp ⟶ Z} (hm : IsSmallMorphism sXm sZ fm) (hp : IsSmallMorphism sXp sZ g)
    (φ : A ⟶ Xp) [IsIso φ] {z : Z} (hz : z ∈ (badLocusBase fm (φ ≫ g) : Set Z)) :
    2 ≤ Order.coheight z := by
  rw [coe_badLocusBase, Set.mem_compl_iff, commonBiregularLocus] at hz
  by_cases h1 : z ∈ biregularLocus fm
  · refine two_le_coheight_of_notMem_biregularLocus hp fun h2 => hz ⟨h1, ?_⟩
    exact biregularLocus_le_biregularLocus_comp φ g h2
  · exact two_le_coheight_of_notMem_biregularLocus hm h1

end BadLocus

/-! ### The flips of a prepared chain -/

section Chain

open MMP.Fourfold.StabilizedSmallKltTail

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a programme
is compatible with their structure morphisms. -/
private theorem eqToHom_comp_modelStr {V : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (sY : ∀ k, Y k ⟶ Spec (.of ℂ)) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V Y) h) ≫ modelStr sV sY b = modelStr sV sY a := by
  subst h; simp

/-- The morphism `V_{k+1} ⟶ T_k` of the `k`-th flip of the `i`-th bridge of a terminal chain is
proper and birational, and lies over `ℂ`. -/
private theorem flipTargetMapOf_properties {T : StabilizedSmallKltTail} (C : TerminalChain T)
    (i : ℕ) (k : Fin (C.bridge i).P.m) (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) :
    IsProper (C.flipTargetMapOf i k d) ∧ IsBirationalMorphism (C.flipTargetMapOf i k d) ∧
      C.flipTargetMapOf i k d ≫ (C.bridge i).P.sT k =
        C.modelStructure (C.flipTargetOf i k d) := by
  have hD := (C.bridge i).P.isFourfoldStepDiagram k k.2
  have hsp := hD.isSmallMorphism_plus
  have hZ := hD.isNormalVariety_target
  haveI := C.isIntegral_flipBase i k
  haveI : IsNormal ((C.bridge i).P.T k) := hZ.2
  haveI : LocallyOfFiniteType ((C.bridge i).P.sT k) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian ((C.bridge i).P.T k) :=
    LocallyOfFiniteType.isLocallyNoetherian ((C.bridge i).P.sT k)
  haveI : IsProper ((C.bridge i).P.gp k) := hsp.isProper
  cases d with
  | isTrue h => exact ⟨hsp.isProper, hsp.isBirationalMorphism, hD.comp_eq_plus⟩
  | isFalse h =>
    have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
    let ψ : (C.junction (i + 1)).Y ≅ (C.bridge i).P.Y k := (C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)
    change IsProper (ψ.hom ≫ (C.bridge i).P.gp k) ∧
      IsBirationalMorphism (ψ.hom ≫ (C.bridge i).P.gp k) ∧
      (ψ.hom ≫ (C.bridge i).P.gp k) ≫ (C.bridge i).P.sT k = (C.junction (i + 1)).sY
    refine ⟨inferInstance, ?_, ?_⟩
    · exact isBirationalMorphism_comp_of_isBirational _ _
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hsp.isBirationalMorphism)
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          (isBirationalMorphism_of_isIso ψ.hom))
    · rw [Category.assoc, hD.comp_eq_plus]
      change ((C.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)) ≫
        modelStr (C.junction i).sY (C.bridge i).P.sY (k.1 + 1) = (C.junction (i + 1)).sY
      rw [Category.assoc, eqToHom_comp_modelStr _ _ hmk]
      exact (Iso.inv_comp_eq _).2 (C.bridge i).comp_sY.symm

/-- The morphism `Y⁺ ⟶ T_k` of a flip of a bridge is `g_k⁺` precomposed with an
isomorphism. -/
private theorem exists_isIso_flipTargetMap_eq {T : StabilizedSmallKltTail} (C : TerminalChain T)
    (i : ℕ) (k : Fin (C.bridge i).P.m) :
    ∃ (φ : C.model (C.flipTarget i k) ⟶ (C.bridge i).P.Y k) (_ : IsIso φ),
      C.flipTargetMap i k = φ ≫ (C.bridge i).P.gp k := by
  unfold TerminalChain.flipTarget TerminalChain.flipTargetMap
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue h => exact ⟨𝟙 ((C.bridge i).P.Y k), IsIso.id _, (Category.id_comp _).symm⟩
  | isFalse h =>
    let ψ : (C.junction (i + 1)).Y ≅ (C.bridge i).P.Y k := (C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y)
        (by omega : (C.bridge i).P.m = k.1 + 1))
    exact ⟨ψ.hom, ψ.isIso_hom, (Category.assoc _ _ _).symm⟩

/-- Both maps of the step diagram `Y⁻ → Z ← Y⁺` of a flip of a prepared chain are small onto a
normal base, so every point of the bad loci `W⁻ ⊆ Y⁻` and `W⁺ ⊆ Y⁺` has coheight at least
two. -/
private theorem two_le_coheight_of_mem_badLoci {T : StabilizedSmallKltTail} (Q : PreparedChain T)
    (μ : Q.FlipMove) :
    (∀ y ∈ (μ.badLocusSource : Set (Q.chain.model μ.source.1)), 2 ≤ Order.coheight y) ∧
      ∀ y ∈ (μ.badLocusTarget : Set (Q.chain.model μ.target.1)), 2 ≤ Order.coheight y := by
  have hD := (Q.chain.bridge μ.1.1).P.isFourfoldStepDiagram μ.1.2 μ.1.2.2
  have hsm : IsSmallMorphism _ _ μ.sourceMap :=
    (Q.chain.bridge μ.1.1).isSmallMorphism μ.1.2 μ.1.2.2
  have hsp := hD.isSmallMorphism_plus
  have hZ := hD.isNormalVariety_target
  haveI : IsNormal μ.base := hZ.2
  haveI : LocallyOfFiniteType ((Q.chain.bridge μ.1.1).P.sT μ.1.2) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian μ.base :=
    LocallyOfFiniteType.isLocallyNoetherian ((Q.chain.bridge μ.1.1).P.sT μ.1.2)
  obtain ⟨φ, hφ, hft⟩ := exists_isIso_flipTargetMap_eq Q.chain μ.1.1 μ.1.2
  have hft' : μ.targetMap = φ ≫ (Q.chain.bridge μ.1.1).P.gp μ.1.2 := hft
  have hbase : ∀ z ∈ (badLocusBase μ.sourceMap μ.targetMap : Set μ.base),
      2 ≤ Order.coheight z :=
    fun z hz => two_le_coheight_of_mem_badLocusBase hsm hsp φ (hft' ▸ hz)
  exact ⟨fun y hy => two_le_coheight_of_comp_mem (𝟙 _) μ.sourceMap hsm.two_le_codimension hbase
      (by rw [Category.id_comp]; exact hy),
    fun y hy => two_le_coheight_of_comp_mem φ _ hsp.two_le_codimension hbase
      (by rw [← hft']; exact hy)⟩

end Chain

/-! ### Divisors over a variety seen over a birational model -/

section CompProper

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

/-- Pulling valuations back along a surjective ring homomorphism is injective. -/
private theorem comap_injective_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Surjective f) :
    Function.Injective fun ξ : Valuation S (WithZero (Multiplicative ℤ)) => ξ.comap f := by
  intro ξ ξ' h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congrArg (fun ν : Valuation R (WithZero (Multiplicative ℤ)) => ν y) h

/-- If the divisors `D` over `X⁻` and `D'` over `X⁺` give the same valuation of `ℂ(Z)` and the
centre of `D` lies in the bad locus `W⁻`, then the centre of `D'` lies in `W⁺`: their generic
points have the same image in `Z`, and `W^± = (f^±)⁻¹(Z ∖ U)`. -/
private theorem center_subset_badLocusPlus {Xm Xp Z : Scheme.{0}}
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : MMP.Mori.IsVariety ℂ sZ) {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsProper fm] [IsProper fp]
    (hbm : IsBirationalMorphism fm) (hbp : IsBirationalMorphism fp) (hm : fm ≫ sZ = sXm)
    (hp : fp ≫ sZ = sXp) {D : DivisorOver ℂ sXm} {D' : DivisorOver ℂ sXp} (hDp : IsProper D.f)
    (hD'p : IsProper D'.f)
    (hv : haveI := hbm.isDominant; haveI := hbp.isDominant
      D'.valuation.comap (functionFieldMap fp) = D.valuation.comap (functionFieldMap fm))
    (hDW : (D.center : Set Xm) ⊆ badLocusMinus fm fp) :
    (D'.center : Set Xp) ⊆ badLocusPlus fm fp := by
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  have hmem : D.f D.E.genericPoint ∈ (badLocusMinus fm fp : Set Xm) := hDW (by
    rw [D.center_eq_closure_genericPoint]
    exact subset_closure rfl)
  have heq : fp (D'.f D'.E.genericPoint) = fm (D.f D.E.genericPoint) :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hZ
      (D := compProper fp hbp hp D' hD'p) (D' := compProper fm hbm hm D hDp) (by
        rw [valuation_compProper, valuation_compProper, hv])
  rw [D'.center_eq_closure_genericPoint]
  refine (badLocusPlus fm fp).isClosed.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr fun hU => hmem ?_)
  change fm (D.f D.E.genericPoint) ∈ commonBiregularLocus fm fp
  rwa [← heq]

end CompProper

/-! ### Finiteness for a pair of small morphisms -/

section Finiteness

/-- Let `f^± : X^± ⟶ Z` be proper birational morphisms over `ℂ` onto a normal variety whose bad
loci `W^±` consist of points of codimension at least two, and let `(X^±, Θ^±)` be terminal pairs
on projective `ℚ`-factorial fourfolds. Then the normalized divisorial valuations `v` of `ℂ(X⁻)`
with centre in `W⁻` which are exceptional over `X⁻` with `a(v; X⁻, Θ⁻) < 2`, or whose
corresponding valuation `v⁺` of `ℂ(X⁺)` is exceptional over `X⁺` with `a(v⁺; X⁺, Θ⁺) < 2`, form a
finite set. -/
private theorem finite_setOf_isCentre_subset_badLocusMinus {Xm Xp Z : Scheme.{0}}
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
    (hZ : IsNormalVariety ℂ sZ) {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsProper fm] [IsProper fp]
    (hbm : IsBirationalMorphism fm) (hbp : IsBirationalMorphism fp) (hm : fm ≫ sZ = sXm)
    (hp : fp ≫ sZ = sXp)
    (hWm : ∀ x ∈ (badLocusMinus fm fp : Set Xm), 2 ≤ Order.coheight x)
    (hWp : ∀ x ∈ (badLocusPlus fm fp : Set Xp), 2 ≤ Order.coheight x)
    (hYm : MMP.Mori.IsProjectiveVariety ℂ sXm) (hQm : IsQFactorial sXm)
    (hdm : topologicalKrullDim Xm = 4) {Θm : QDivisor Xm} (hΘm : IsKltTerminalPair sXm Θm)
    (hYp : MMP.Mori.IsProjectiveVariety ℂ sXp) (hQp : IsQFactorial sXp)
    (hdp : topologicalKrullDim Xp = 4) {Θp : QDivisor Xp} (hΘp : IsKltTerminalPair sXp Θp) :
    haveI := hbm.isDominant
    haveI := hbp.isDominant
    {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ)) |
      (∃ Zc : IrreducibleCloseds Xm, MMP.Intersection.IsCentre ℂ sXm v Zc ∧
          (Zc : Set Xm) ⊆ badLocusMinus fm fp) ∧
        ∃ v' : Valuation Xp.functionField (WithZero (Multiplicative ℤ)),
          v'.comap (functionFieldMap fp) = v.comap (functionFieldMap fm) ∧
          ((MMP.Intersection.IsExceptionalValuation ℂ sXm v ∧
              ∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy sXm Θm v a) ∨
            (MMP.Intersection.IsExceptionalValuation ℂ sXp v' ∧
              ∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy sXp Θp v' a))}.Finite := by
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
  obtain ⟨Fm, hFm, hcm⟩ := exists_finite_of_two_le_coheight sXm hdm (badLocusMinus fm fp) hWm
  obtain ⟨Fp, hFp, hcp⟩ := exists_finite_of_two_le_coheight sXp hdp (badLocusPlus fm fp) hWp
  have hAm := IsKltTerminalPair.finite_setOf_three_le_codimension_centre hYm hQm hdm hΘm
    (L := Θm.support) subset_rfl
  have hBm := (hFm.inter_of_left {V | topologicalKrullDim (V : Set Xm) = 2}).biUnion
    fun V hV => IsKltTerminalPair.finite_setOf_isCentre_of_hasLogDiscrepancy_lt_two hYm hQm hdm
      hΘm (L := Θm.support) subset_rfl V hV.2
  have hAp := IsKltTerminalPair.finite_setOf_three_le_codimension_centre hYp hQp hdp hΘp
    (L := Θp.support) subset_rfl
  have hBp := (hFp.inter_of_left {V | topologicalKrullDim (V : Set Xp) = 2}).biUnion
    fun V hV => IsKltTerminalPair.finite_setOf_isCentre_of_hasLogDiscrepancy_lt_two hYp hQp hdp
      hΘp (L := Θp.support) subset_rfl V hV.2
  have hinj := comap_injective_of_surjective hbm.functionFieldMap_bijective.2
  refine ((hAm.union hBm).union (((hAp.union hBp).image
    fun v' => v'.comap (functionFieldMap fp)).preimage hinj.injOn)).subset ?_
  rintro v ⟨⟨Zc, hZc, hZW⟩, v', hv', ⟨hexc, h⟩ | ⟨hexc, h⟩⟩
  · rcases hcm Zc hZW with hcod | ⟨hZF, hZ2⟩
    · exact Or.inl (Or.inl ⟨hexc, h, Zc, hZc, hcod⟩)
    · exact Or.inl (Or.inr (Set.mem_biUnion (x := Zc) ⟨hZF, hZ2⟩ ⟨hexc, hZc, h⟩))
  · obtain ⟨D', hD'p, hv'D', -⟩ := id hexc
    obtain ⟨D, hDp, hvD, hZD⟩ := hZc
    have hZ'c : MMP.Intersection.IsCentre ℂ sXp v' D'.center := ⟨D', hD'p, hv'D', rfl⟩
    have hZ'W := center_subset_badLocusPlus hZ.1 hbm hbp hm hp hDp hD'p
      (by rw [← hv'D', ← hvD, hv']) (hZD ▸ hZW)
    refine Or.inr ⟨v', ?_, hv'⟩
    rcases hcp _ hZ'W with hcod | ⟨hZF, hZ2⟩
    · exact Or.inl ⟨hexc, h, _, hZ'c, hcod⟩
    · exact Or.inr (Set.mem_biUnion (x := D'.center) ⟨hZF, hZ2⟩ ⟨hexc, hZ'c, h⟩)

end Finiteness

/-! ### The weighted bad set of a flip -/

open MMP.Fourfold.StabilizedSmallKltTail in
/-- **The weighted bad set of a flip is finite.** For a small terminal flip `μ` of a bridge of a
prepared chain `Q`, the weighted bad set `Q.flipBadSet μ` is finite. -/
private theorem solution {T : MMP.Fourfold.StabilizedSmallKltTail}
    (Q : MMP.Fourfold.StabilizedSmallKltTail.PreparedChain T) (μ : Q.FlipMove) :
    (Q.flipBadSet μ).Finite := by
  have hD := (Q.chain.bridge μ.1.1).P.isFourfoldStepDiagram μ.1.2 μ.1.2.2
  haveI : IsProper ((Q.chain.bridge μ.1.1).P.g μ.1.2) :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper μ.sourceMap :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  obtain ⟨hpp, hbp, hp⟩ := flipTargetMapOf_properties Q.chain μ.1.1 μ.1.2 inferInstance
  haveI : IsProper μ.targetMap := hpp
  obtain ⟨hWm, hWp⟩ := two_le_coheight_of_mem_badLoci Q μ
  obtain ⟨hΘm, hQm, hYm, hdm⟩ :=
    TerminalChain.isKltTerminalPair_modelBoundary Q.chain μ.source.1
  obtain ⟨hΘp, hQp, hYp, hdp⟩ :=
    TerminalChain.isKltTerminalPair_modelBoundary Q.chain μ.target.1
  refine (finite_setOf_isCentre_subset_badLocusMinus hD.isNormalVariety_target
    hD.isBirationalMorphism_minus hbp hD.comp_eq_minus hp hWm hWp hYm hQm hdm hΘm hYp hQp hdp
    hΘp).subset ?_
  have hlt : ∀ {a : ℝ} {w : ℕ}, 0 < w → w = MMP.Fourfold.difficultyWeight Q.scale (2 - a) →
      a < 2 := fun {a} {w} hw hwa => by
    by_contra hle
    simp [hwa, MMP.Fourfold.difficultyWeight, max_eq_right (show 2 - a ≤ 0 by linarith)] at hw
  rintro v ⟨hc, v', hv', w, w', hw, hw', hpos⟩
  refine ⟨hc, v', hv', ?_⟩
  rcases Nat.eq_zero_or_pos w with hw0 | hw0
  · obtain ⟨hexc, a, ⟨n, D, -, hDv, hl⟩, hwa⟩ := hw'
    exact Or.inr ⟨hexc, a, hlt (by omega) hwa, n, D, hDv, hl⟩
  · obtain ⟨hexc, a, ⟨n, D, -, hDv, hl⟩, hwa⟩ := hw
    exact Or.inl ⟨hexc, a, hlt hw0 hwa, n, D, hDv, hl⟩

end Proof_lem_oai4_c3_flip_bad_set_finite

end

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-- The weighted bad set `𝒜₀` of a small terminal flip of a bridge of a prepared chain is
finite. -/
@[mmp "lem_oai4_c3_flip_bad_set_finite"]
public theorem finite_flipBadSet {T : StabilizedSmallKltTail} (Q : PreparedChain T)
    (μ : Q.FlipMove) : (Q.flipBadSet μ).Finite :=
      by revert T Q μ; exact Proof_lem_oai4_c3_flip_bad_set_finite.solution

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
