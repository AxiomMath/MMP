module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.MMP.Flip.TrivialFlopPullback
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.TriviallyConnectedContractible

/-!
# The contracting chain of FA 15.9 has projective models and flop targets

Let `(X, Δ)` satisfy the assumptions of the abundance theorem FA 15.4 over `ℂ`, with
`L = K + Δ` not eventually free and composed of a pencil, and let `D` be an `L`-trivially
connected prime divisor. Granted the termination of `H`-flops
(`MMP.Flips.HFlopSequencesTerminate`), the construction of FA 15.9 produces flops
`X = X₀ ⤏ X₁ ⤏ ⋯ ⤏ X_m` of `(K_i + Δ_i)`-trivial flop data
`φ_i : X_i ⟶ T_i ⟵ X_{i+1} : φ_i⁺`, followed by a birational contraction `c : X_m ⟶ X'` of the
transform of `D`. Every model `X_i` and every base `T_i` of this chain is a normal projective
variety. On each base the adjoint `K_{T_i} + Δ_{T_i}` has a Cartier multiple pulling back to the
same multiple of `K_i + Δ_i` and of `K_{i+1} + Δ_{i+1}`, so eventual freeness, and being
eventually free and composed of a pencil, pass in both directions through every flop.

## Implementation notes

Stated over `ℂ`, with the termination of `H`-flops (`MMP.Flips.HFlopSequencesTerminate`) as a
hypothesis. The chain is the one of
`MMP.Flips.exists_trivialFlop_chain_projective_of_isTriviallyConnected`; on each flop the descent
of the adjoints is `MMP.Flips.IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne`. The
transform of a divisor along the flop `p_i` is `φ_i⁺⁻¹_* ∘ φ_{i*}`, since `p_i` lies over `T_i`
and is a morphism in codimension one.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.4.4, 15.9
-/

public section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.FourfoldProofs.FourfoldFa15ContractibleChainProjectiveTargetsProof

/-- The generic point of a prime divisor lies in no closed set of codimension at least two. -/
public theorem genericPoint_notMem_of_two_le_closedsCodimension {X : Scheme.{0}}
    (Z : TopologicalSpace.Closeds X) (hZ : 2 ≤ closedsCodimension Z)
    (P : MMP.Mori.PrimeDivisor X) : P.genericPoint ∉ Z := by
  intro hP
  have hsub : ((irreducibleSetEquivPoints (α := X)).symm P.genericPoint : Set X) ⊆ Z :=
    Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hP)
  have h2 := le_closedsCodimension_iff.mp hZ _ hsub
  rw [codimension_eq_coheight, Order.coheight_orderIso, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- An isomorphism in codimension one maps the generic point of a prime divisor to a point of
coheight one. -/
public theorem coheight_map_genericPoint_of_isIsoInCodimOne {X T : Scheme.{0}} {f : X ⟶ T}
    (hf : IsIsoInCodimOne f) (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (f P.genericPoint) = 1 := by
  obtain ⟨V, W, hV, -, hle, hiso⟩ := hf
  let U : X.Opens := V.compl
  let U' : T.Opens := W.compl
  let p : U.toScheme := ⟨P.genericPoint, genericPoint_notMem_of_two_le_closedsCodimension V hV P⟩
  have hfp : U'.ι (f.resLE U' U hle p) = f P.genericPoint := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    rfl
  rw [← hfp, Topology.IsOpenEmbedding.coheight_eq _ U'.ι.isOpenEmbedding,
    Topology.IsOpenEmbedding.coheight_eq _ (f.resLE U' U hle).isOpenEmbedding,
    ← Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding]
  exact P.coheight_genericPoint

/-- A rational map `ρ : X ⤏ Y` over `T`, defined in codimension one, with `f : X ⟶ T` an
isomorphism in codimension one and `g : Y ⟶ T` proper birational onto the normal `T`, transforms
each prime divisor `P` to the prime divisor `g⁻¹_* f_* P`. -/
public theorem exists_transformPrimeDivisor_eq_some {X Y T : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] [IsSeparated (T ↘ Limits.terminal Scheme)]
    {f : X ⟶ T} {g : Y ⟶ T} [IsProper g] (hg : IsBirationalMorphism g)
    (hf : IsIsoInCodimOne f) {ρ : X.RationalMap Y} (hρ : RationalMap.IsOver f g ρ)
    (hρc : RationalMap.IsMorphismInCodimOne ρ) (P : MMP.Mori.PrimeDivisor X) :
    ∃ (DT : MMP.Mori.PrimeDivisor T) (DY : MMP.Mori.PrimeDivisor Y),
      RationalMap.transformPrimeDivisor f.toRationalMap P = some DT ∧
      inverseTransformPrimeDivisor g DT = some DY ∧
      RationalMap.transformPrimeDivisor ρ P = some DY := by
  have e : ∀ p : (g ⁻¹ᵁ biregularLocus g).toScheme,
      (biregularLocus g).ι ((g ∣_ biregularLocus g) p) = g ((g ⁻¹ᵁ biregularLocus g).ι p) :=
    fun p => by rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hT1 := coheight_map_genericPoint_of_isIsoInCodimOne hf P
  let DT : MMP.Mori.PrimeDivisor T :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne (f P.genericPoint) hT1
  have hDT : MMP.Mori.PrimeDivisor.genericPoint DT = f P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hT1
  have htB : f P.genericPoint ∈ biregularLocus g :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg hT1.le
  obtain ⟨q, hq⟩ := (g ∣_ biregularLocus g).surjective ⟨f P.genericPoint, htB⟩
  have hgq : g q.1 = f P.genericPoint := by
    have := e q
    rw [hq] at this
    exact this.symm
  have hy1 : Order.coheight q.1 = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (show g q.1 ∈ _ from hgq ▸ htB),
      hgq, hT1]
  let DY : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne q.1 hy1
  have hDY : MMP.Mori.PrimeDivisor.genericPoint DY = q.1 :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy1
  have hξd : P.genericPoint ∈ RationalMap.dom ρ := by
    by_contra h
    exact genericPoint_notMem_of_two_le_closedsCodimension (RationalMap.dom ρ).compl hρc P h
  obtain ⟨g', hξg', hg'⟩ := RationalMap.definedAt_iff.mp hξd
  have hy' : g (g'.hom ⟨P.genericPoint, hξg'⟩) = f P.genericPoint :=
    MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq (g := g'.compHom g)
      (g' := f.toPartialMap) (by rw [Scheme.RationalMap.compHom_toRationalMap, hg']; exact hρ)
      hξg' trivial
  have hy'y : g'.hom ⟨P.genericPoint, hξg'⟩ = q.1 :=
    congrArg Subtype.val (show (⟨_, show g _ ∈ biregularLocus g from hy' ▸ htB⟩ :
        (g ⁻¹ᵁ biregularLocus g).toScheme) = q from
      (g ∣_ biregularLocus g).isOpenEmbedding.injective
        ((biregularLocus g).ι.isOpenEmbedding.injective
          ((e _).trans ((hy'.trans hgq.symm).trans (e q).symm))))
  refine ⟨DT, DY,
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P DT).mpr hDT.symm,
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (by rw [hDY, hgq, hDT]) (by rw [hDY, hgq]; exact htB),
    RationalMap.transformPrimeDivisor_eq_some_iff.mpr
      ⟨RationalMap.definedAt_iff.mpr ⟨g', hξg', hg'⟩, ?_⟩⟩
  have hc : RationalMap.transform ρ P.idealSheaf.support = DY.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hξg', hy'y, ← hDY]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure DY).symm
  have := DY.integral
  rw [RationalMap.transformIdeal, hc, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- A rational map `ρ : X ⤏ Y` over `T`, defined in codimension one, between integral schemes,
with `f : X ⟶ T` an isomorphism in codimension one and `g : Y ⟶ T` proper birational onto the
normal `T`, transforms divisors as `g⁻¹_* ∘ f_*`. -/
public theorem transformDivisor_eq_inverseTransformDivisor {X Y T : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] [IsSeparated (T ↘ Limits.terminal Scheme)]
    {f : X ⟶ T} {g : Y ⟶ T} [IsProper g] (hg : IsBirationalMorphism g)
    (hf : IsIsoInCodimOne f) {ρ : X.RationalMap Y} (hρ : RationalMap.IsOver f g ρ)
    (hρc : RationalMap.IsMorphismInCodimOne ρ) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor ρ D =
      inverseTransformDivisor g (RationalMap.transformDivisor f.toRationalMap D) := by
  have : (RationalMap.transformDivisor ρ : DivisorWithCoeffs R X →+ _) =
      (inverseTransformDivisor g).comp (RationalMap.transformDivisor f.toRationalMap) := by
    refine Finsupp.addHom_ext fun P r => ?_
    obtain ⟨DT, DY, h1, h2, h3⟩ := exists_transformPrimeDivisor_eq_some hg hf hρ hρc P
    rw [AddMonoidHom.comp_apply, RationalMap.transformDivisor_single_of_eq_some h3,
      RationalMap.transformDivisor_single_of_eq_some h1,
      inverseTransformDivisor_single_of_eq_some h2]
  exact DFunLike.congr_fun this D

end MMP.FourfoldProofs.FourfoldFa15ContractibleChainProjectiveTargetsProof

end

public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori MMP.Fourfold MMP.FourfoldProofs.FourfoldFa15ContractibleChainProjectiveTargetsProof

/-- A scheme separated over `Spec ℂ` is separated over the terminal scheme. -/
public theorem isSeparated_terminal_from_of_isSeparated {Y : Scheme.{0}} (s : Y ⟶ Spec (.of ℂ))
    (hs : IsSeparated s) : IsSeparated (Y ↘ Limits.terminal Scheme) := by
  rw [show (Y ↘ Limits.terminal Scheme) = s ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- **The contracting chain of FA 15.9 with projective flop targets** (FA 15.4.4, 15.9). Let
`(X, Δ)` satisfy the assumptions of FA 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`) over `ℂ`,
with `K + Δ` not eventually free and composed of a pencil (`MMP.Flips.IsEventuallyFreePencil`),
and let `D` be a `(K + Δ)`-trivially connected prime divisor (`MMP.Flips.IsTriviallyConnected`).
Assume that sequences of `H`-flops terminate (`MMP.Flips.HFlopSequencesTerminate`).

Then the conclusions of
`MMP.Flips.IsTriviallyConnected.exists_isBirationalContraction_of_hFlopSequencesTerminate`
hold for a chain of flops `p_i : X_i ⤏ X_{i+1}` of trivial flop data `φ_i : X_i ⟶ T_i`,
`φ_i⁺ : X_{i+1} ⟶ T_i` (`i < m`) and a contraction `c : X_m ⟶ X'`, in which moreover:
* every model `X_i` (`i ≤ m`) is a normal projective variety, and every base `T_i` (`i < m`) is
  a normal projective variety;
* for each `i < m` there are `r > 0` and a Cartier divisor `M` on `T_i` with
  `M = r (φ_{i*} K_i + φ_{i*} Δ_i)`, `φ_i^* M = r (K_i + Δ_i)` and
  `φ_i⁺^* M = r (K_{i+1} + Δ_{i+1})`;
* for each `i < m`, `K_i + Δ_i` is eventually free (`MMP.Flips.IsEventuallyFree`) iff
  `K_{i+1} + Δ_{i+1}` is, and eventually free and composed of a pencil iff
  `K_{i+1} + Δ_{i+1}` is. -/
public theorem
    IsTriviallyConnected.exists_isBirationalContraction_isProjectiveVariety_of_hFlopSequencesTerminate
    (hterm : HFlopSequencesTerminate) {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (hA : SatisfiesAbundanceAssumptions ℂ sX K Δ)
    (hL : ¬ IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ))
    {D : Mori.PrimeDivisor X} (hD : IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single D 1)) :
    ∃ (m : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
      (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
      (KY : ∀ i, Divisor (Y i)) (ΔY : ∀ i, QDivisor (Y i)) (DY : ∀ i, Divisor (Y i))
      (T : ℕ → Scheme.{0}) (sT : ∀ i, T i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (T i)) (_ : ∀ i, CompactSpace (T i))
      (_ : ∀ i, IsLocallyNoetherian (T i)) (_ : ∀ i, IsNormal (T i))
      (φ : ∀ i, modelSeq X Y i ⟶ T i)
      (φp : ∀ i, Y i ⟶ T i) (p : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ m, Mori.IsProjectiveVariety ℂ (modelStr sX sY i)) ∧
      (∀ i < m, IsTrivialFlop ℂ (modelStr sX sY i) (sY i) (sT i) 3 (divisorSeq K KY i)
          (divisorSeq Δ ΔY i) (φ i) (φp i) (p i) ∧
        KY i = RationalMap.transformDivisor (p i) (divisorSeq K KY i) ∧
        ΔY i = flopDivisor (p i) (divisorSeq Δ ΔY i) ∧
        DY i = RationalMap.transformDivisor (p i)
          (divisorSeq (Finsupp.single D 1 : Divisor X) DY i) ∧
        Mori.IsProjectiveVariety ℂ (sT i) ∧
        (∃ r : ℕ, 0 < r ∧ ∃ M : Divisor (T i), M.IsCartier ∧
          Divisor.toQDivisor M = (r : ℤ) •
            (Divisor.toQDivisor (RationalMap.transformDivisor (φ i).toRationalMap
              (divisorSeq K KY i)) + flopBaseDivisor (φ i) (divisorSeq Δ ΔY i)) ∧
          (∃ (MX : Divisor (modelSeq X Y i)) (hB : ∀ Z : irreducibleComponents (modelSeq X Y i),
              φ i (componentGenericPoint (modelSeq X Y i) Z) ∉ M.supp),
            Divisor.toQDivisor MX =
                (r : ℤ) • (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ∧
              M.IsPullback (φ i) hB MX) ∧
          (∃ (MY : Divisor (Y i)) (hB : ∀ Z : irreducibleComponents (Y i),
              φp i (componentGenericPoint (Y i) Z) ∉ M.supp),
            Divisor.toQDivisor MY = (r : ℤ) • (Divisor.toQDivisor (KY i) + ΔY i) ∧
              M.IsPullback (φp i) hB MY)) ∧
        (IsEventuallyFree ℂ (modelStr sX sY i)
            (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ↔
          IsEventuallyFree ℂ (sY i) (Divisor.toQDivisor (KY i) + ΔY i)) ∧
        (IsEventuallyFreePencil ℂ (modelStr sX sY i)
            (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ↔
          IsEventuallyFreePencil ℂ (sY i) (Divisor.toQDivisor (KY i) + ΔY i))) ∧
      ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (c : modelSeq X Y m ⟶ X')
        (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
        (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX'),
        IsBirationalContraction ℂ sX' (modelStr sX sY m) c ∧ IsBirationalMorphism c ∧
        exceptionalSet c =
          ((divisorSeq (Finsupp.single D 1 : Divisor X) DY m).supp : Set (modelSeq X Y m)) ∧
        (∃ (hc : ∀ Z : irreducibleComponents (modelSeq X Y m),
            c (componentGenericPoint (modelSeq X Y m) Z) ∉
              (Divisor.toQDivisor (RationalMap.transformDivisor c.toRationalMap
                (divisorSeq K KY m)) +
                RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).supp)
            (B : QDivisor (modelSeq X Y m)),
          (Divisor.toQDivisor (RationalMap.transformDivisor c.toRationalMap (divisorSeq K KY m)) +
              RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).IsPullback c hc B ∧
            (Divisor.toQDivisor (divisorSeq K KY m) + divisorSeq Δ ΔY m).QLinearlyEquivalent B) ∧
        picardNumber sX' + 1 = picardNumber sX ∧
        SatisfiesAbundanceAssumptions ℂ sX'
          (RationalMap.transformDivisor c.toRationalMap (divisorSeq K KY m))
          (RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)) := by
  classical
  obtain ⟨m, Y, sY, i₁, i₂, i₃, i₄, i₅, i₆, KY, ΔY, P, T, sT, j₁, j₂, j₃, j₄, j₅, φ, φp, p, hA',
    hflop, hfin⟩ := exists_trivialFlop_chain_projective_of_isTriviallyConnected hterm hA hL hD
  have hlft : ∀ i, LocallyOfFiniteType (modelStr sX sY i) := fun i => match i with
    | 0 => inferInstanceAs (LocallyOfFiniteType sX)
    | j + 1 => i₅ j
  have hproj : ∀ i ≤ m, Mori.IsProjectiveVariety ℂ (modelStr sX sY i) := fun i hi =>
    match i, hi with
    | 0, _ => hA.isProjectiveVariety
    | j + 1, hj => (hA' j hj).1.isProjectiveVariety
  have hklt : ∀ i < m, IsKawamataLogTerminal (modelStr sX sY i) 3 (divisorSeq K KY i)
      (QDivisor.toRDivisor (divisorSeq Δ ΔY i)) := fun i hi =>
    match i, hi with
    | 0, _ => hA.isKawamataLogTerminal
    | j + 1, hj => (hA' j (by omega)).1.isKawamataLogTerminal
  refine ⟨m, Y, sY, i₁, i₂, i₃, i₄, KY, ΔY, fun j => Finsupp.single (P j) 1, T, sT, j₁, j₂, j₃,
    j₄, φ, φp, p, hproj, fun i hi => ?_, hfin⟩
  obtain ⟨⟨hd, hover⟩, hK, hΔ, hP, hTp, -⟩ := hflop i hi
  have hsmall := hd.isSmall
  haveI : IsProper (φ i) := hsmall.isProper
  haveI : IsProper (φp i) := hd.isProper_flop
  have := isSeparated_terminal_from_of_isSeparated (sY i) hd.isNormalVariety_flop.1.toIsSeparated
  have := isSeparated_terminal_from_of_isSeparated (sT i) hTp.toIsVariety.toIsSeparated
  have hρc : RationalMap.IsMorphismInCodimOne (p i) :=
    RationalMap.isMorphismInCodimOne_of_isOver
      (show Mori.IsNormalVariety ℂ (modelStr sX sY i) from ⟨hsmall.isVariety_source, inferInstance⟩)
      (φ i) (φp i) (p i) hover
  have htr : ∀ {R : Type} [AddCommMonoid R] (E : DivisorWithCoeffs R (modelSeq X Y i)),
      RationalMap.transformDivisor (p i) E =
        inverseTransformDivisor (φp i) (RationalMap.transformDivisor (φ i).toRationalMap E) :=
    fun E => transformDivisor_eq_inverseTransformDivisor
      hd.isBirationalMorphism_flop hsmall.exists_isIso hover hρc E
  have hKY : KY i = inverseTransformDivisor (φp i)
      (RationalMap.transformDivisor (φ i).toRationalMap (divisorSeq K KY i)) := hK.trans (htr _)
  have hΔY : ΔY i = inverseTransformDivisor (φp i) (flopBaseDivisor (φ i) (divisorSeq Δ ΔY i)) :=
    hΔ.trans (htr _)
  obtain ⟨-, ⟨r, hr, M, hM, hMc, hMX, hMY⟩, -, hfree, -, hpencil⟩ :=
    IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne (hproj i hi.le)
      (hA' i hi).1.isProjectiveVariety hTp hsmall.comp_eq hd.comp_eq_flop hd.isBirationalMorphism
      hd.isBirationalMorphism_flop hsmall.exists_isIso hd.isIsoInCodimOne_flop (hklt i hi)
      hd.isNumericallyTrivialOver
  refine ⟨⟨hd, hover⟩, hK, hΔ, hP, hTp, ?_, ?_, ?_⟩ <;> rw [hKY, hΔY]
  exacts [⟨r, hr, M, hMc, hM, hMX, hMY⟩, hfree, hpencil]

end MMP.Flips

end
