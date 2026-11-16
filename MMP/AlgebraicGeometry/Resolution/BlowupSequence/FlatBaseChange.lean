module

public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.Restriction
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition

/-!
# Blow-up sequences under flat base change: reduced pull-backs and transforms

Let `𝐁 = (X_i, Z_i)` be a blow-up sequence starting with `X` and `h : Y → X` a morphism. The
reduced pull-back `(h^*𝐁)^red` deletes the steps whose pulled-back centre `h_i⁻¹Z_i` is empty;
it ends in a scheme `Y'` which in general differs from the end of `h^*𝐁`, and it comes with a
last morphism `h' : Y' → X_r` over `h`. When `h` is flat the square formed by `Y' → Y`, `h'`, `h`
and `X_r → X` is cartesian, as for the pull-back itself: blowing up commutes with flat base
change, and a blow-up whose centre has empty inverse image is an isomorphism over the image of
`h`.

Along a smooth blow-up sequence of order `m` the controlled transform `π⁻¹_{Z*}I` is the
residual of `π^*I` by the `m`-th power of the exceptional divisor. Both are compatible with
inverse images, so if `𝐁` is of order `m` starting with `(X, I, E)` and `(h^*𝐁)^red` is of order
`m` starting with `(Y, h^*I, E_Y)`, the controlled transform of `h^*I` along `(h^*𝐁)^red` is the
inverse image of that of `I` along `𝐁`.

For `h` flat with reduced base changes (smooth morphisms, projections of a change of perfect
base field) the reduced closures, closures and inverse images the other constructions are made
of commute with `h`. Hence the total transform of an ordered divisor along one blow-up pulls
back, provided the components of the centre do; along a blow-up whose centre has empty inverse
image it pulls back to `h⁻¹E` followed by an empty entry. The scheme-theoretic image of a reduced
subscheme pulls back along a cartesian square, so the extension by closure along a quasi-compact
open immersion commutes with `h`; and, for flat `h`, the restriction of `h^*𝐁` to `h⁻¹H` is the
base change of `𝐁|_H`, so the birational transform `H'` of `H` pulls back.

## Main definitions

* `MMP.Resolution.ClosedBlowupSequence.pullbackReducedWithHom`: the reduced pull-back together
  with its last morphism.
* `MMP.Resolution.ClosedBlowupSequence.pullbackReducedHom`: the last morphism
  `(h^*𝐁)^red → X_r`.
* `MMP.Resolution.ClosedBlowupSequence.HasReducedCentres`: every centre is reduced.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.pullbackReducedHom_toBase_comm`: the last morphism lies
  over `h`.
* `MMP.Resolution.Kollar.isPullback_pullbackReduced_toBase_of_flat`: for flat `h` the end of
  `(h^*𝐁)^red` is `X_r ×_X Y`.
* `MMP.Resolution.ClosedBlowupSequence.append_pullbackReduced`: the reduced pull-back of a
  concatenation is the concatenation of the reduced pull-backs.
* `MMP.Resolution.Kollar.controlledTransform_comap_canonicalLift`: one blow-up of order `m`
  commutes with inverse images.
* `MMP.Resolution.Kollar.controlledTransform_pullbackReduced`: the controlled transform along
  the reduced pull-back of a sequence of order `m`.
* `MMP.Resolution.Kollar.totalTransform_comap_canonicalLift`,
  `MMP.Resolution.Kollar.totalTransform_comap_blowUpLift`: the total transform of an ordered
  divisor along one blow-up.
* `MMP.Resolution.Kollar.comap_map_eq_map_comap_of_isPullback`: the scheme-theoretic image of
  a reduced subscheme under flat base change.
* `MMP.Resolution.Kollar.extendByClosure_pullback`: the extension by closure commutes with
  flat base change.
* `MMP.Resolution.Kollar.ker_restrictHom_pullback`: the birational transform of a closed
  subscheme commutes with flat base change.
* `MMP.Resolution.ClosedBlowupSequence.isOrderMTripleSeq_append_iff`: concatenations of
  sequences of order `m`.

## Implementation notes

The reduced pull-back and its last morphism are computed together, as a dependent pair, by
`ClosedBlowupSequence.pullbackReducedWithHom`; its first component is
`ClosedBlowupSequence.pullbackReduced`, and `ClosedBlowupSequence.pullbackReducedHom` is its
second component transported along this equality. Statements by induction on the sequence are
made for the pair, whose recursion matches the sequence.

The controlled transform along a sequence is compared with the help of the order-`m` hypothesis
on both sides, rather than through the behaviour of orders under `h`: the controlled transform
on `Y` is determined by `h^*I` and the exceptional divisor once the order along each pulled-back
centre is known to be `m`, and the order-`m` property of the sequence on `Y` says so.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.30, 3.32, 3.58, 3.104]
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral CategoryTheory.catToReflQuiver

universe u

namespace MMP.Resolution

namespace ClosedBlowupSequence

/-! ### The last morphism of the reduced pull-back -/

open Classical in
/-- The reduced pull-back `(h^*𝐁)^red` of a blow-up sequence along `h : Y → X`, together with its
last morphism `h' : Y' → X_r`: a step whose pulled-back centre is empty is skipped, `h_i` being
lifted to `X_{i+1}`, and otherwise `h_{i+1}` is the canonical lift of `h_i`. -/
noncomputable def pullbackReducedWithHom : {X Y : Scheme.{u}} → (B : ClosedBlowupSequence X) →
    (h : Y ⟶ X) → Σ C : ClosedBlowupSequence Y, C.target ⟶ B.target
  | _, Y, nil _, h => ⟨nil Y, h⟩
  | _, _, cons Z B, h =>
      if hZ : Z.comap h = ⊤ then
        B.pullbackReducedWithHom (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ))
      else ⟨cons (Z.comap h) (B.pullbackReducedWithHom (canonicalLift h Z)).1,
        (B.pullbackReducedWithHom (canonicalLift h Z)).2⟩

/-- If the inverse image of the first centre `Z` under `h` is empty, the reduced pull-back of
`cons Z B` along `h` is that of `B` along the lift of `h` to the blow-up of `Z`. -/
theorem pullbackReducedWithHom_cons_of_eq_top {X Y : Scheme.{u}} (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) (h : Y ⟶ X) (hZ : Z.comap h = ⊤) :
    (cons Z B).pullbackReducedWithHom h =
      B.pullbackReducedWithHom (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ)) :=
  dite_eq_left hZ

/-- If the inverse image of the first centre `Z` under `h` is non-empty, the reduced pull-back of
`cons Z B` along `h` blows up `h⁻¹Z` and continues with that of `B` along the canonical lift. -/
theorem pullbackReducedWithHom_cons_of_ne_top {X Y : Scheme.{u}} (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) (h : Y ⟶ X) (hZ : Z.comap h ≠ ⊤) :
    (cons Z B).pullbackReducedWithHom h =
      ⟨cons (Z.comap h) (B.pullbackReducedWithHom (canonicalLift h Z)).1,
        (B.pullbackReducedWithHom (canonicalLift h Z)).2⟩ :=
  dite_eq_right hZ

/-- The first component of `pullbackReducedWithHom` is the reduced pull-back. -/
theorem pullbackReducedWithHom_fst {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (h : Y ⟶ X), (B.pullbackReducedWithHom h).1 = B.pullbackReduced h := by
  induction B with
  | nil X => intro Y h; rfl
  | cons Z B ih =>
    intro Y h
    by_cases hZ : Z.comap h = ⊤
    · rw [pullbackReducedWithHom_cons_of_eq_top Z B h hZ]
      simp only [pullbackReduced, hZ, dite_true]
      exact ih _
    · rw [pullbackReducedWithHom_cons_of_ne_top Z B h hZ]
      simp only [pullbackReduced, hZ, dite_false]
      exact congrArg (cons _) (ih _)

/-- The last morphism `h' : Y' → X_r` of the reduced pull-back `(h^*𝐁)^red`, `Y'` its end. -/
noncomputable def pullbackReducedHom {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) : (B.pullbackReduced h).target ⟶ B.target :=
  eqToHom (congrArg target (B.pullbackReducedWithHom_fst h).symm) ≫
    (B.pullbackReducedWithHom h).2

/-- A dependent pair whose first component is `C'` is the pair `⟨C', f⟩` for the transported
second component. -/
theorem sigma_eq_mk_eqToHom {Y T : Scheme.{u}} (p : Σ C : ClosedBlowupSequence Y, C.target ⟶ T)
    {C' : ClosedBlowupSequence Y} (e : p.1 = C') :
    p = ⟨C', eqToHom (congrArg target e.symm) ≫ p.2⟩ := by
  obtain ⟨C, f⟩ := p
  subst e
  simp

/-- `pullbackReducedWithHom` is the pair of the reduced pull-back and its last morphism. -/
theorem pullbackReducedWithHom_eq {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) : B.pullbackReducedWithHom h = ⟨B.pullbackReduced h, B.pullbackReducedHom h⟩ :=
  sigma_eq_mk_eqToHom _ (B.pullbackReducedWithHom_fst h)

/-- The second component of `pullbackReducedWithHom` lies over `h`. -/
theorem pullbackReducedWithHom_toBase_comm {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (h : Y ⟶ X),
      (B.pullbackReducedWithHom h).1.toBase ≫ h = (B.pullbackReducedWithHom h).2 ≫ B.toBase := by
  induction B with
  | nil X =>
    intro Y h
    change 𝟙 Y ≫ h = h ≫ 𝟙 X
    simp
  | cons Z B ih =>
    intro Y h
    by_cases hZ : Z.comap h = ⊤
    · rw [pullbackReducedWithHom_cons_of_eq_top Z B h hZ]
      change _ = _ ≫ B.toBase ≫ blowUpToBase Z
      rw [← Category.assoc, ← ih, Category.assoc, blowUpLift_comp]
    · rw [pullbackReducedWithHom_cons_of_ne_top Z B h hZ]
      change ((B.pullbackReducedWithHom (canonicalLift h Z)).1.toBase ≫
        blowUpToBase (Z.comap h)) ≫ h = _ ≫ B.toBase ≫ blowUpToBase Z
      rw [← Category.assoc, ← ih, Category.assoc, Category.assoc,
        canonicalLift_comp_blowUpToBase]

/-- The last morphism of the reduced pull-back lies over `h`: `Π_r ∘ h' = h ∘ Π^Y`. -/
theorem pullbackReducedHom_toBase_comm {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) : (B.pullbackReduced h).toBase ≫ h = B.pullbackReducedHom h ≫ B.toBase := by
  have := B.pullbackReducedWithHom_toBase_comm h
  rw [B.pullbackReducedWithHom_eq h] at this
  exact this

/-! ### Concatenations -/

/-- The first component of `pullbackReducedWithHom` of a concatenation is the concatenation of
the first components. -/
theorem pullbackReducedWithHom_append_fst {X : Scheme.{u}} (D : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (C : ClosedBlowupSequence D.target) (h : Y ⟶ X),
      ((D.append C).pullbackReducedWithHom h).1 =
        (D.pullbackReducedWithHom h).1.append
          (C.pullbackReducedWithHom (D.pullbackReducedWithHom h).2).1 := by
  induction D with
  | nil X => intro Y C h; rfl
  | cons Z D ih =>
    intro Y C h
    change ((cons Z (D.append C)).pullbackReducedWithHom h).1 = _
    by_cases hZ : Z.comap h = ⊤
    · rw [pullbackReducedWithHom_cons_of_eq_top Z _ h hZ,
        pullbackReducedWithHom_cons_of_eq_top Z D h hZ]
      exact ih C _
    · rw [pullbackReducedWithHom_cons_of_ne_top Z _ h hZ,
        pullbackReducedWithHom_cons_of_ne_top Z D h hZ]
      exact congrArg (cons _) (ih C _)

/-- **The reduced pull-back of a concatenation** is the concatenation of the reduced pull-back
of the first sequence and the reduced pull-back of the second along the last morphism of the
first: `((𝐃 ⋅ 𝐂)^*_h)^red = (h^*𝐃)^red ⋅ (h'^*𝐂)^red`. -/
theorem append_pullbackReduced {X Y : Scheme.{u}} (D : ClosedBlowupSequence X)
    (C : ClosedBlowupSequence D.target) (h : Y ⟶ X) :
    (D.append C).pullbackReduced h =
      (D.pullbackReduced h).append (C.pullbackReduced (D.pullbackReducedHom h)) := by
  rw [← pullbackReducedWithHom_fst (D.append C), pullbackReducedWithHom_append_fst,
    pullbackReducedWithHom_fst C]
  exact congrArg (fun p : Σ C' : ClosedBlowupSequence Y, C'.target ⟶ D.target =>
    p.1.append (C.pullbackReduced p.2)) (D.pullbackReducedWithHom_eq h)

/-- If no centre of `𝐁` is empty and no pulled-back centre is empty either (for instance for `h`
flat and surjective), the reduced pull-back with its last morphism is the pull-back with its
last morphism. -/
theorem pullbackReducedWithHom_eq_of_forall {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (P : ∀ {X Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (hP : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) (Z : X.IdealSheafData), P h → Z ≠ ⊤ →
      Z.comap h ≠ ⊤ ∧ P (canonicalLift h Z)) (hB : B.HasNoEmptyBlowups) :
    ∀ {Y : Scheme.{u}} (h : Y ⟶ X), P h →
      B.pullbackReducedWithHom h = ⟨B.pullback h, B.pullbackHom h⟩ := by
  induction B with
  | nil X => intro Y h _; rfl
  | cons Z B ih =>
    intro Y h hh
    obtain ⟨hZ, hl⟩ := hP h Z hh hB.1
    rw [pullbackReducedWithHom_cons_of_ne_top Z B h hZ, ih hB.2 _ hl]
    rfl

/-! ### Reduced centres and the extension by closure -/

/-- Every centre `Z_i` of the blow-up sequence is a reduced closed subscheme. -/
def HasReducedCentres : {X : Scheme.{u}} → ClosedBlowupSequence X → Prop
  | _, nil _ => True
  | _, cons Z B => IsReduced Z.subscheme ∧ B.HasReducedCentres

@[simp]
theorem hasReducedCentres_nil (X : Scheme.{u}) : (nil X).HasReducedCentres :=
  trivial

@[simp]
theorem hasReducedCentres_cons_iff {X : Scheme.{u}} (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) :
    (cons Z B).HasReducedCentres ↔ IsReduced Z.subscheme ∧ B.HasReducedCentres :=
  Iff.rfl

/-- The first step of the extension by closure, when `ι⁻¹(ι_*Z) = Z`. -/
theorem extendByClosure_cons_of_comap_map_eq {U X : Scheme.{u}} (Z : U.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) (ι : U ⟶ X) (hc : (Z.map ι).comap ι = Z) :
    (cons Z B).extendByClosure ι = cons (Z.map ι)
      (B.extendByClosure (eqToHom (congrArg blowUp hc.symm) ≫ canonicalLift ι (Z.map ι))) :=
  dite_eq_left hc

/-- Pulling back along a morphism precomposed with an `eqToHom`. -/
theorem pullback_eqToHom_comp_heq {X Y Y' : Scheme.{u}} (S : ClosedBlowupSequence X)
    (e : Y = Y') (f : Y' ⟶ X) : S.pullback (eqToHom e ≫ f) ≍ S.pullback f := by
  subst e
  simp

/-- The canonical lift along equal morphisms. -/
theorem canonicalLift_congr {X Y : Scheme.{u}} {f f' : Y ⟶ X} (e : f = f')
    (Z : X.IdealSheafData) :
    canonicalLift f Z = eqToHom (by rw [e]) ≫ canonicalLift f' Z := by
  subst e
  simp

/-! ### Concatenations of sequences of order `m` -/

section OrderM

variable {k : Type u} [Field k]

/-- A concatenation is a smooth blow-up sequence of order `m` starting with `(X, I, E)` exactly
when its first part is one and its second part is one starting with the end
`(X_r, I_r, E_r)` of the first. -/
theorem isOrderMTripleSeq_append_iff (m : ℕ) : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (C : ClosedBlowupSequence B.target) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (E : OrderedDivisor X),
    (B.append C).IsOrderMTripleSeq s I E m ↔ B.IsOrderMTripleSeq s I E m ∧
      C.IsOrderMTripleSeq (B.toBase ≫ s) (B.controlledTransform I) (B.orderedTotalTransform E) m
  | _, nil _, C, s, I, E => by
    change C.IsOrderMTripleSeq s I E m ↔ _ ∧ C.IsOrderMTripleSeq (𝟙 _ ≫ s) I E m
    rw [Category.id_comp]
    refine ⟨fun hC => ⟨?_, hC⟩, And.right⟩
    cases C with
    | nil => exact hC
    | cons Z C => exact hC.1
  | _, cons Z B, C, s, I, E => by
    change (cons Z (B.append C)).IsOrderMTripleSeq s I E m ↔ _
    have ih := isOrderMTripleSeq_append_iff m B C (blowUpToBase Z ≫ s)
      (MMP.Resolution.controlledTransform Z I) (E.totalTransform Z)
    change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (B.append C).IsOrderMTripleSeq _ _ _ m) ↔
      (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ B.IsOrderMTripleSeq _ _ _ m) ∧
        C.IsOrderMTripleSeq ((B.toBase ≫ blowUpToBase Z) ≫ s) _ _ m
    rw [ih, Category.assoc]
    tauto

/-- The end of a smooth blow-up sequence of order `m` starting with a triple is a triple. -/
theorem isTriple_end_of_isOrderMTripleSeq (m : ℕ) : ∀ {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (E : OrderedDivisor X), B.IsOrderMTripleSeq s I E m →
      IsTriple (B.toBase ≫ s) (B.controlledTransform I) (B.orderedTotalTransform E)
  | _, nil _, s, I, E, h => by
    change IsTriple (𝟙 _ ≫ s) I E
    rwa [Category.id_comp]
  | _, cons Z B, s, I, E, h => by
    have := isTriple_end_of_isOrderMTripleSeq m B _ _ _ h.2.2.2.2.2
    change IsTriple ((B.toBase ≫ blowUpToBase Z) ≫ s) _ _
    rwa [Category.assoc]

/-- The centres of a smooth blow-up sequence of order `m` are reduced. -/
theorem hasReducedCentres_of_isOrderMTripleSeq (m : ℕ) : ∀ {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (E : OrderedDivisor X), B.IsOrderMTripleSeq s I E m → B.HasReducedCentres
  | _, nil _, _, _, _, _ => trivial
  | _, cons Z B, s, I, E, h => by
    obtain ⟨⟨-, -, hlft, -⟩, hZ, -, -, -, hB⟩ := h
    have := hlft
    exact ⟨Aux.isReduced_subscheme_of_isSmoothScheme s Z hZ,
      hasReducedCentres_of_isOrderMTripleSeq m B _ _ _ hB⟩

end OrderM

/-- Appending to a concatenation is appending to its first part. -/
theorem exists_append_append_eq {X : Scheme.{u}} (D : ClosedBlowupSequence X) :
    ∀ (C : ClosedBlowupSequence D.target) (A : ClosedBlowupSequence (D.append C).target),
      ∃ C' : ClosedBlowupSequence D.target, (D.append C).append A = D.append C' := by
  induction D with
  | nil X => intro C A; exact ⟨C.append A, rfl⟩
  | cons Z D ih =>
    intro C A
    obtain ⟨C', hC'⟩ := ih C A
    exact ⟨C', congrArg (cons Z) hC'⟩

/-- The first `j` steps `Π_{(j)}` of the divisor separation sequence are a first part of
`Π_{(j + i)}`. -/
theorem exists_divisorSeparationAux_add_eq_append (M : MarkedFamily.{u}) (m : ℕ)
    (t : FieldBlowupTriple.{u}) (j : ℕ) : ∀ i : ℕ, ∃ C : ClosedBlowupSequence
      (divisorSeparationAux M m t j).target,
      divisorSeparationAux M m t (j + i) = (divisorSeparationAux M m t j).append C := by
  have hnil : ∀ {X : Scheme.{u}} (D : ClosedBlowupSequence X), D.append (nil _) = D := by
    intro X D
    induction D with
    | nil X => rfl
    | cons Z D ih => exact congrArg (cons Z) ih
  intro i
  induction i with
  | zero => exact ⟨nil _, (hnil _).symm⟩
  | succ i ih =>
    obtain ⟨C, hC⟩ := ih
    have key : ∀ (P : ClosedBlowupSequence t.X), P = (divisorSeparationAux M m t j).append C →
        ∃ C' : ClosedBlowupSequence (divisorSeparationAux M m t j).target,
          (open Classical in if IsTriple (t.endOf P).sX (t.endOf P).I (t.endOf P).E then
            P.append (bdFunctor M (dimNat t.X) m (j + i) (t.endOf P)) else P) =
            (divisorSeparationAux M m t j).append C' := by
      rintro P rfl
      split_ifs
      · exact exists_append_append_eq _ C _
      · exact ⟨C, rfl⟩
    rw [← Nat.add_assoc]
    exact key _ hC

/-! ### Iterated pull-backs with their last morphisms -/

/-- Blow-up sequences with equal first centres and equal remaining pairs are equal pairs. -/
theorem sigma_cons_eq_of_heq {Y T : Scheme.{u}} {c c' : Y.IdealSheafData} (hc : c = c')
    {B : ClosedBlowupSequence (blowUp c)} {B' : ClosedBlowupSequence (blowUp c')}
    {f : B.target ⟶ T} {f' : B'.target ⟶ T}
    (hB : (⟨B, f⟩ : Σ D : ClosedBlowupSequence (blowUp c), D.target ⟶ T) ≍
      (⟨B', f'⟩ : Σ D : ClosedBlowupSequence (blowUp c'), D.target ⟶ T)) :
    (⟨cons c B, f⟩ : Σ D : ClosedBlowupSequence Y, D.target ⟶ T) = ⟨cons c' B', f'⟩ := by
  subst hc
  cases eq_of_heq hB
  rfl

/-- The pull-back along `k` of the pull-back along `h`, with the composite of the last
morphisms, is the pull-back along `k ≫ h` with its last morphism. -/
theorem pullback_pullback_sigma_heq {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    ∀ {W Y Y' : Scheme.{u}} (h : W ⟶ X) (k : Y ⟶ W) (k' : Y' ⟶ X) (e : Y = Y'),
      eqToHom e ≫ k' = k ≫ h →
      (⟨(S.pullback h).pullback k, (S.pullback h).pullbackHom k ≫ S.pullbackHom h⟩ :
          Σ C : ClosedBlowupSequence Y, C.target ⟶ S.target) ≍
        (⟨S.pullback k', S.pullbackHom k'⟩ :
          Σ C : ClosedBlowupSequence Y', C.target ⟶ S.target) := by
  induction S with
  | nil X =>
    intro W Y Y' h k k' e hk
    subst e
    simp only [eqToHom_refl, Category.id_comp] at hk
    subst hk
    rfl
  | cons Z S ih =>
    intro W Y Y' h k k' e hk
    subst e
    simp only [eqToHom_refl, Category.id_comp] at hk
    subst hk
    refine heq_of_eq (sigma_cons_eq_of_heq (Scheme.IdealSheafData.comap_comp Z k h).symm ?_)
    exact ih _ _ _ (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z k h).symm)
      (canonicalLift_comp_canonicalLift h k Z).symm

end ClosedBlowupSequence

namespace Kollar

open ClosedBlowupSequence

/-! ### Flat base change -/

/-- Blowing up a centre with empty inverse image: `B_{h⁻¹Z}Y → Y` is an isomorphism. -/
theorem isIso_blowUpToBase_comap_of_eq_top {X Y : Scheme.{u}} (h : Y ⟶ X)
    (Z : X.IdealSheafData) (hZ : Z.comap h = ⊤) : IsIso (blowUpToBase (Z.comap h)) := by
  rw [hZ]
  exact isIso_blowUpToBase_top Y

/-- When `h⁻¹Z = ∅`, the lift `Y → B_ZX` of `h` is the inverse of `B_{h⁻¹Z}Y ≅ Y` followed by the
canonical lift. -/
theorem blowUpLift_eq_inv_comp_canonicalLift {X Y : Scheme.{u}} (h : Y ⟶ X)
    (Z : X.IdealSheafData) (hZ : Z.comap h = ⊤) [IsIso (blowUpToBase (Z.comap h))] :
    blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ) =
      inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z :=
  (blowUpLift_unique Z h (isCartierOver_of_comap_eq_top h Z hZ)
    (inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z) (by
    rw [Category.assoc, canonicalLift_comp_blowUpToBase, IsIso.inv_hom_id_assoc])).symm

/-- For flat `h` with `h⁻¹Z = ∅`, the square formed by `𝟙_Y`, the lift `Y → B_ZX`, `h` and
`B_ZX → X` is cartesian. -/
theorem isPullback_blowUpLift_of_flat {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    (Z : X.IdealSheafData) (hZ : Z.comap h = ⊤) :
    IsPullback (𝟙 Y) (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ)) h
      (blowUpToBase Z) := by
  have := isIso_blowUpToBase_comap_of_eq_top h Z hZ
  rw [blowUpLift_eq_inv_comp_canonicalLift h Z hZ]
  have sq1 : IsPullback (inv (blowUpToBase (Z.comap h)))
      (inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z) (canonicalLift h Z) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := sq1.paste_horiz (isPullback_canonicalLift_of_flat h Z)
  simpa using this

/-- For flat `h` with `h⁻¹Z = ∅`, the lift `Y → B_ZX` of `h` is flat. -/
theorem flat_blowUpLift {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h] (Z : X.IdealSheafData)
    (hZ : Z.comap h = ⊤) : Flat (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ)) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_blowUpLift_of_flat h Z hZ) ‹_›

/-- For flat `h`, the square of the reduced pull-back, as a pair, is cartesian. -/
theorem isPullback_pullbackReducedWithHom_of_flat {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) : ∀ {Y : Scheme.{u}} (h : Y ⟶ X) [Flat h],
      IsPullback (B.pullbackReducedWithHom h).1.toBase (B.pullbackReducedWithHom h).2 h
        B.toBase := by
  induction B with
  | nil X =>
    intro Y h _
    change IsPullback (𝟙 Y) h h (𝟙 X)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  | cons Z B ih =>
    intro Y h _
    by_cases hZ : Z.comap h = ⊤
    · rw [pullbackReducedWithHom_cons_of_eq_top Z B h hZ]
      have := flat_blowUpLift h Z hZ
      have hsq := (ih (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ))).paste_horiz
        (isPullback_blowUpLift_of_flat h Z hZ)
      rw [Category.comp_id] at hsq
      exact hsq
    · rw [pullbackReducedWithHom_cons_of_ne_top Z B h hZ]
      have := flat_canonicalLift h Z
      exact (ih (canonicalLift h Z)).paste_horiz (isPullback_canonicalLift_of_flat h Z)

/-- **The reduced pull-back along a flat morphism is base change**: for flat `h : Y → X` the
square formed by `Y' → Y`, the last morphism `h' : Y' → X_r` of `(h^*𝐁)^red`, `h` and
`Π_r : X_r → X` is cartesian, `Y' = X_r ×_X Y`. -/
theorem isPullback_pullbackReduced_toBase_of_flat {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) [Flat h] :
    IsPullback (B.pullbackReduced h).toBase (B.pullbackReducedHom h) h B.toBase := by
  have := isPullback_pullbackReducedWithHom_of_flat B h
  rw [B.pullbackReducedWithHom_eq h] at this
  exact this

/-- The last morphism of the reduced pull-back along a flat morphism is flat. -/
theorem flat_pullbackReducedHom {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X)
    [Flat h] : Flat (B.pullbackReducedHom h) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_pullbackReduced_toBase_of_flat B h) ‹_›

/-- The last morphism of the reduced pull-back along a smooth morphism is smooth. -/
theorem smooth_pullbackReducedHom {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X)
    [Smooth h] : Smooth (B.pullbackReducedHom h) :=
  MorphismProperty.of_isPullback (P := @Smooth) (isPullback_pullbackReduced_toBase_of_flat B h) ‹_›

/-- If `h` is flat with reduced base changes, so is the last morphism of the reduced pull-back. -/
theorem isReducedFlatBaseChange_pullbackReducedHom {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h) :
    IsReducedFlatBaseChange (B.pullbackReducedHom h) :=
  have := hh.flat
  hh.of_isPullback (isPullback_pullbackReduced_toBase_of_flat B h)

/-- For flat surjective `h` and `𝐁` without empty blow-ups, the reduced pull-back with its last
morphism is the pull-back with its last morphism. -/
theorem pullbackReducedWithHom_eq_of_flat_of_surjective {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) (hB : B.HasNoEmptyBlowups) (h : Y ⟶ X) [Flat h]
    [Surjective h] : B.pullbackReducedWithHom h = ⟨B.pullback h, B.pullbackHom h⟩ := by
  refine B.pullbackReducedWithHom_eq_of_forall (fun h => Flat h ∧ Surjective h)
    (fun h Z hh hZ => ?_) hB h ⟨‹_›, ‹_›⟩
  obtain ⟨_, _⟩ := hh
  refine ⟨fun hZh => hZ ?_, flat_canonicalLift h Z,
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_canonicalLift_of_flat h Z) ‹_›⟩
  rw [← Scheme.IdealSheafData.support_eq_bot_iff] at hZh ⊢
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := h.surjective x
  have : y ∈ ((Z.comap h).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  rwa [hZh] at this

/-! ### Controlled transforms of order `m` -/

section ControlledTransform

variable {k k' : Type u} [Field k] [Field k']

/-- Along a smooth centre of constant order `m`, the divisor of the controlled transform is the
`m`-th power of the exceptional divisor. -/
theorem controlledTransformDivisorIdeal_eq_pow_of_orderAlongEq {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hI : OrderAlongEq I (Z.support : Set X) m) :
    controlledTransformDivisorIdeal Z I = Z.comap (blowUpToBase Z) ^ m := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  let _ : Fintype (componentsOf (Z.support : Set X)) :=
    Fintype.ofFinite (componentsOf (Z.support : Set X))
  refine IdealSheafData.eq_of_stalk_eq _ _ fun y => ?_
  set x := blowUpToBase Z y
  have hD : IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
      ∏ W : componentsOf (Z.support : Set X), Ideal.map ((blowUpToBase Z).stalkMap y).hom
        (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^
          (orderAlong I W.2.1.1).toNat := by
    unfold controlledTransformDivisorIdeal
    rw [finprod_eq_prod_of_fintype, stalk_prod]
    refine Finset.prod_congr rfl fun W _ => ?_
    rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
  rw [hD, IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
  by_cases hx : x ∈ (Z.support : Set X)
  · obtain ⟨W0, hW0, hxW0, huniq, hstalk, -⟩ := exists_component_through sX hX Z hZ I x hx
    rw [Finset.prod_eq_single (⟨W0, hW0⟩ : componentsOf (Z.support : Set X))]
    · rw [hstalk, hI W0 hW0]
      rfl
    · intro W _ hne
      have : x ∉ (W : Set X) := fun hxW => hne (Subtype.ext (huniq W W.2 hxW))
      simp [Ideal.map_top, stalk_componentsFamily_eq_top Z W.2 this]
    · simp
  · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx]
    refine (Finset.prod_eq_one fun W _ => ?_).trans (by simp [Ideal.map_top, Ideal.top_pow])
    simp [Ideal.map_top, stalk_componentsFamily_eq_top Z W.2 fun hxW => hx (W.2.1.2 hxW)]

/-- Along a smooth centre `Z` of constant order `m`, the controlled transform multiplied by the
`m`-th power of the exceptional divisor is `π^*I`. -/
theorem controlledTransform_mul_pow_eq {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (hord : OrderAlongEq I (Z.support : Set X) m) :
    controlledTransform Z I * Z.comap (blowUpToBase Z) ^ m = I.comap (blowUpToBase Z) := by
  rw [← controlledTransformDivisorIdeal_eq_pow_of_orderAlongEq sX hX Z hZ I m hord]
  exact controlledTransform_mul_eq sX hX Z hZ hcodim I hI

/-- **One blow-up of order `m` commutes with inverse images.** Let `X` be smooth over `k`, `Z` a
smooth centre with components of positive codimension along which `ord I = m`, and `h : Y → X`
a morphism from a smooth scheme over a field `k'` such that `h⁻¹Z` is again such a centre for
`h^*I`. Then the controlled transform of `h^*I` along `h⁻¹Z` is the inverse image of the
controlled transform of `I` along the canonical lift `B_{h⁻¹Z}Y → B_ZX`. -/
theorem controlledTransform_comap_canonicalLift {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX] (h : Y ⟶ X)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (hord : OrderAlongEq I (Z.support : Set X) m)
    (sY : Y ⟶ Spec (.of k')) (hY : MMP.Mori.IsSmoothScheme sY) [LocallyOfFiniteType sY]
    [QuasiCompact sY] (hZY : MMP.Mori.IsSmoothScheme ((Z.comap h).subschemeι ≫ sY))
    (hcodimY : HasComponentsOfPositiveCodim ((Z.comap h).support : Set Y))
    (hIY : IsNonzeroAtGenericPoints (I.comap h))
    (hordY : OrderAlongEq (I.comap h) ((Z.comap h).support : Set Y) m) :
    controlledTransform (Z.comap h) (I.comap h) =
      (controlledTransform Z I).comap (canonicalLift h Z) := by
  have hDc : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Z.comap h).comap (blowUpToBase (Z.comap h)) ^ m) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap h)) m
  have h1 := controlledTransform_mul_pow_eq sY hY (Z.comap h) hZY hcodimY (I.comap h) hIY m hordY
  have h2 := controlledTransform_mul_pow_eq sX hX Z hZ hcodim I hI m hord
  have hc := canonicalLift_comp_blowUpToBase h Z
  have hF : (Z.comap h).comap (blowUpToBase (Z.comap h)) =
      (Z.comap (blowUpToBase Z)).comap (canonicalLift h Z) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hc]
  have h3 : (controlledTransform Z I).comap (canonicalLift h Z) *
      (Z.comap h).comap (blowUpToBase (Z.comap h)) ^ m =
      (I.comap h).comap (blowUpToBase (Z.comap h)) := by
    rw [hF, ← Stacks.IdealSheaf.comap_pow, ← Stacks.IdealSheaf.comap_mul, h2,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hc]
  refine Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor hDc ?_
  rw [mul_comm, h1, ← h3, mul_comm]

/-- **A blow-up of order `m` whose centre has empty inverse image.** If `h⁻¹Z = ∅`, the inverse
image of the controlled transform `π⁻¹_{Z*}I` along the lift `Y → B_ZX` of `h` is `h^*I`. -/
theorem comap_blowUpLift_controlledTransform {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX] (h : Y ⟶ X)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (hord : OrderAlongEq I (Z.support : Set X) m)
    (hZh : Z.comap h = ⊤) :
    (controlledTransform Z I).comap (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZh)) =
      I.comap h := by
  have h2 := congrArg (fun J => J.comap (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZh)))
    (controlledTransform_mul_pow_eq sX hX Z hZ hcodim I hI m hord)
  rw [Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, blowUpLift_comp,
    hZh] at h2
  have htop : (⊤ : Y.IdealSheafData) = 1 := rfl
  rwa [htop, one_pow, mul_one] at h2

/-- The controlled transform along the reduced pull-back, for the pair. -/
theorem controlledTransform_pullbackReducedWithHom {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) : ∀ {Y : Scheme.{u}} (h : Y ⟶ X) (sX : X ⟶ Spec (.of k))
      (sY : Y ⟶ Spec (.of k')) (I : X.IdealSheafData) (J : Y.IdealSheafData)
      (E : OrderedDivisor X) (E' : OrderedDivisor Y) (m : ℕ),
      B.IsOrderMTripleSeq sX I E m → (B.pullbackReducedWithHom h).1.IsOrderMTripleSeq sY J E' m →
      J = I.comap h →
      (B.pullbackReducedWithHom h).1.controlledTransform J =
        (B.controlledTransform I).comap (B.pullbackReducedWithHom h).2 := by
  induction B with
  | nil X =>
    intro Y h sX sY I J E E' m _ _ hJ
    exact hJ
  | cons Z B ih =>
    intro Y h sX sY I J E E' m hX hY hJ
    obtain ⟨⟨-, hXs, hlft, hqc, -, hI, -⟩, hZ, hcodim, -, hord, hB⟩ := hX
    have := hlft
    have := hqc
    by_cases hZh : Z.comap h = ⊤
    · rw [pullbackReducedWithHom_cons_of_eq_top Z B h hZh] at hY ⊢
      exact ih _ _ sY _ J _ E' m hB hY
        (hJ.trans (comap_blowUpLift_controlledTransform sX hXs h Z hZ hcodim I hI m hord hZh).symm)
    · rw [pullbackReducedWithHom_cons_of_ne_top Z B h hZh] at hY ⊢
      obtain ⟨⟨-, hYs, hlftY, hqcY, -, hIY, -⟩, hZY, hcodimY, -, hordY, hC⟩ := hY
      have := hlftY
      have := hqcY
      subst hJ
      exact ih _ _ _ _ _ _ _ m hB hC
        (controlledTransform_comap_canonicalLift sX hXs h Z hZ hcodim I hI m hord sY hYs hZY
          hcodimY hIY hordY)

/-- **The controlled transform along the reduced pull-back.** Let `𝐁` be a smooth blow-up
sequence of order `m` starting with `(X, I, E)` and `h : Y → X` a morphism such that the
reduced pull-back `(h^*𝐁)^red` is a smooth blow-up sequence of order `m` starting with
`(Y, h^*I, E_Y)` (over some field). Then the last controlled transform of `h^*I` along
`(h^*𝐁)^red` is the inverse image of the last controlled transform of `I` along the last
morphism `h' : Y' → X_r`. -/
theorem controlledTransform_pullbackReduced {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k')) (I : X.IdealSheafData)
    (E : OrderedDivisor X) (E' : OrderedDivisor Y) (m : ℕ) (hX : B.IsOrderMTripleSeq sX I E m)
    (hY : (B.pullbackReduced h).IsOrderMTripleSeq sY (I.comap h) E' m) :
    (B.pullbackReduced h).controlledTransform (I.comap h) =
      (B.controlledTransform I).comap (B.pullbackReducedHom h) := by
  rw [← B.pullbackReducedWithHom_fst h] at hY
  have key := controlledTransform_pullbackReducedWithHom B h sX sY I _ E E' m hX hY rfl
  rw [B.pullbackReducedWithHom_eq h] at key
  exact key

end ControlledTransform

/-! ### Total transforms of ordered divisors -/

section TotalTransform

/-- The entries of the total transform `π⁻¹_tot(E)` other than the last one. -/
theorem totalTransform_E_castSucc {X : Scheme.{u}} (E : OrderedDivisor X)
    (Z : X.IdealSheafData) (i : Fin E.s) :
    (E.totalTransform Z).E i.castSucc = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (blowUpToBase Z ⁻¹' (((E.E i).support : Set X) \
        componentsOfCodimAtLeastTwo (Z.support : Set X)))) := by
  simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc]

/-- The last entry of the total transform `π⁻¹_tot(E)`. -/
theorem totalTransform_E_last {X : Scheme.{u}} (E : OrderedDivisor X)
    (Z : X.IdealSheafData) :
    (E.totalTransform Z).E (Fin.last E.s) = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W)) := by
  simp only [OrderedDivisor.totalTransform, Fin.snoc_last]

/-- The support of `h⁻¹E` is the inverse image of the support of `E`. -/
theorem support_comap {X Y : Scheme.{u}} (E : OrderedDivisor X) (h : Y ⟶ X) :
    (E.comap h).support = h ⁻¹' E.support := by
  simp only [OrderedDivisor.support, OrderedDivisor.comap, Set.preimage_iUnion,
    Scheme.IdealSheafData.support_comap]
  rfl

/-- The reduced closure of `π⁻¹(T)` pulls back along the canonical lift of a flat morphism with
reduced base changes to the reduced closure of `π'⁻¹(h⁻¹T)`. -/
theorem comap_canonicalLift_vanishingIdeal_closure {X Y : Scheme.{u}} {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (Z : X.IdealSheafData) (T : Set X) :
    (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (blowUpToBase Z ⁻¹' T))).comap (canonicalLift h Z) =
      Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (blowUpToBase (Z.comap h) ⁻¹' (h ⁻¹' T))) := by
  have hl := hh.canonicalLift Z
  have := hl.universallyOpen
  refine hl.comap_vanishingIdeal _ _ ?_
  rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure,
    ((canonicalLift h Z).isOpenMap).preimage_closure_eq_closure_preimage
      (canonicalLift h Z).continuous]
  congr 1
  rw [← Set.preimage_comp, ← Set.preimage_comp]
  congr 1
  funext y
  have := congrArg (fun f : blowUp (Z.comap h) ⟶ X => f y)
    (canonicalLift_comp_blowUpToBase h Z)
  simpa using this.symm

/-- **The total transform under a flat base change with reduced base changes, one blow-up.**
For `h : Y → X` flat with reduced base changes, the inverse image of `π⁻¹_tot(E)` along the
canonical lift `B_{h⁻¹Z}Y → B_ZX` is `π'⁻¹_tot(h⁻¹E)`, provided the two pieces of `Z` the total
transform is built from pull back: the union `Z^{≥2}` of the components of codimension `≥ 2`,
and the union of the components of `Z` that are not components of `Supp E`. -/
theorem totalTransform_comap_canonicalLift {X Y : Scheme.{u}} {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (E : OrderedDivisor X) (Z : X.IdealSheafData)
    (h2 : componentsOfCodimAtLeastTwo ((Z.comap h).support : Set Y) =
      h ⁻¹' componentsOfCodimAtLeastTwo (Z.support : Set X))
    (hlast : (⋃ (W : Set Y) (_ : W ∈ componentsOf ((Z.comap h).support : Set Y))
        (_ : W ∉ componentsOf (E.comap h).support), W) =
      h ⁻¹' ⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf E.support), W) :
    (E.totalTransform Z).comap (canonicalLift h Z) = (E.comap h).totalTransform (Z.comap h) := by
  have hent : ∀ i, ((E.totalTransform Z).E i).comap (canonicalLift h Z) =
      ((E.comap h).totalTransform (Z.comap h)).E i := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      have hr := totalTransform_E_last (E.comap h) (Z.comap h)
      have hl : (⋃ (W : Set Y) (_ : W ∈ componentsOf ((Z.comap h).support : Set Y))
          (_ : W ∉ componentsOf (E.comap h).support), blowUpToBase (Z.comap h) ⁻¹' W) =
          blowUpToBase (Z.comap h) ⁻¹' (h ⁻¹' ⋃ (W : Set X)
            (_ : W ∈ componentsOf (Z.support : Set X)) (_ : W ∉ componentsOf E.support), W) := by
        rw [← hlast]
        simp only [Set.preimage_iUnion]
      have hX : (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W) =
          blowUpToBase Z ⁻¹' ⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
            (_ : W ∉ componentsOf E.support), W := by
        simp only [Set.preimage_iUnion]
      change _ = ((E.comap h).totalTransform (Z.comap h)).E (Fin.last (E.comap h).s)
      rw [totalTransform_E_last, hr, hl, hX]
      exact comap_canonicalLift_vanishingIdeal_closure hh Z _
    | cast i =>
      have hEi : (((E.E i).comap h).support : Set Y) = h ⁻¹' ((E.E i).support : Set X) := by
        rw [Scheme.IdealSheafData.support_comap]; rfl
      have hr := totalTransform_E_castSucc (E.comap h) (Z.comap h) i
      change _ = ((E.comap h).totalTransform (Z.comap h)).E (Fin.castSucc (n := (E.comap h).s) i)
      rw [totalTransform_E_castSucc, hr]
      change _ = Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
        (blowUpToBase (Z.comap h) ⁻¹' ((((E.E i).comap h).support : Set Y) \
          componentsOfCodimAtLeastTwo ((Z.comap h).support : Set Y))))
      rw [h2, hEi, ← Set.preimage_sdiff]
      exact comap_canonicalLift_vanishingIdeal_closure hh Z _
  change (⟨E.s + 1, fun i => ((E.totalTransform Z).E i).comap (canonicalLift h Z)⟩ :
    OrderedDivisor _) = ⟨E.s + 1, ((E.comap h).totalTransform (Z.comap h)).E⟩
  congr 1
  funext i
  exact hent i

/-- **The total transform along a blow-up whose centre has empty inverse image.** For
`h : Y → X` flat with reduced base changes, `h⁻¹Z = ∅` and `E` with reduced entries, the inverse
image of `π⁻¹_tot(E) = (E^1′, …, E^s′, F)` along the lift `Y → B_ZX` of `h` is
`(h⁻¹E^1, …, h⁻¹E^s, ∅)`. -/
theorem totalTransform_comap_blowUpLift {X Y : Scheme.{u}} {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (E : OrderedDivisor X)
    (hE : ∀ i, IsReduced (E.E i).subscheme) (Z : X.IdealSheafData) (hZ : Z.comap h = ⊤) :
    (E.totalTransform Z).comap (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ)) =
      ⟨E.s + 1, Fin.snoc (α := fun _ => Y.IdealSheafData) (fun i => (E.E i).comap h) ⊤⟩ := by
  classical
  set L := blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ) with hLdef
  have hL : IsReducedFlatBaseChange L := by
    have := isIso_blowUpToBase_comap_of_eq_top h Z hZ
    rw [hLdef, blowUpLift_eq_inv_comp_canonicalLift h Z hZ]
    exact IsReducedFlatBaseChange.of_isPullback
      (IsPullback.of_horiz_isIso (fst := inv (blowUpToBase (Z.comap h)))
        (snd := inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z) (f := canonicalLift h Z)
        (g := 𝟙 _) ⟨by simp⟩) (hh.canonicalLift Z)
  have hopen : IsOpenMap L := by
    have := hL.universallyOpen
    exact L.isOpenMap
  have hLπ : ∀ S : Set X, ⇑L ⁻¹' (⇑(blowUpToBase Z) ⁻¹' S) = ⇑h ⁻¹' S := by
    intro S
    rw [← Set.preimage_comp]
    congr 1
    funext y
    have := congrArg (fun f : Y ⟶ X => f y) (blowUpLift_comp Z h
      (isCartierOver_of_comap_eq_top h Z hZ))
    simpa using this
  have hZe : ⇑h ⁻¹' (Z.support : Set X) = ∅ := by
    have := congrArg (fun I : Y.IdealSheafData => (I.support : Set Y)) hZ
    simp only [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_top] at this
    exact this
  have hsub : ∀ W ∈ componentsOf (Z.support : Set X), ⇑h ⁻¹' W = ∅ := fun W hW =>
    Set.eq_empty_of_subset_empty ((Set.preimage_mono hW.1.2).trans hZe.le)
  have hentry : ∀ i : Fin E.s, ((E.totalTransform Z).E i.castSucc).comap L = (E.E i).comap h := by
    intro i
    have := hE i
    have hEi : E.E i = Scheme.IdealSheafData.vanishingIdeal (E.E i).support :=
      Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
    have hcl : IsClosed (⇑h ⁻¹' ((E.E i).support : Set X)) :=
      (E.E i).support.isClosed.preimage h.continuous
    have h1 : (E.E i).comap h = Scheme.IdealSheafData.vanishingIdeal ⟨_, hcl⟩ := by
      conv_lhs => rw [hEi]
      exact hh.comap_vanishingIdeal _ _ rfl
    rw [h1, totalTransform_E_castSucc]
    refine hL.comap_vanishingIdeal _ _ ?_
    rw [TopologicalSpace.Closeds.coe_closure,
      hopen.preimage_closure_eq_closure_preimage L.continuous, hLπ, Set.preimage_sdiff]
    have hZ2 : ⇑h ⁻¹' componentsOfCodimAtLeastTwo (Z.support : Set X) = ∅ := by
      refine Set.eq_empty_of_subset_empty ?_
      intro y hy
      simp only [componentsOfCodimAtLeastTwo, Set.preimage_iUnion, Set.mem_iUnion] at hy
      obtain ⟨W, hW, -, hyW⟩ := hy
      rw [hsub W hW] at hyW
      exact hyW
    rw [hZ2, Set.sdiff_empty, hcl.closure_eq]
    rfl
  have hlast : ((E.totalTransform Z).E (Fin.last E.s)).comap L = ⊤ := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_bot (X := Y), totalTransform_E_last]
    refine hL.comap_vanishingIdeal _ _ ?_
    rw [TopologicalSpace.Closeds.coe_closure,
      hopen.preimage_closure_eq_closure_preimage L.continuous]
    simp only [Set.preimage_iUnion, hLπ]
    have : (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf E.support), ⇑h ⁻¹' W) = ∅ := by
      refine Set.eq_empty_of_subset_empty ?_
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨W, hW, -, hyW⟩ := hy
      rw [hsub W hW] at hyW
      exact hyW
    rw [this, closure_empty]
    rfl
  change (⟨E.s + 1, fun i => ((E.totalTransform Z).E i).comap L⟩ : OrderedDivisor _) = _
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => rwa [Fin.snoc_last]
  | cast i =>
    rw [Fin.snoc_castSucc]
    exact hentry i

end TotalTransform

/-! ### Scheme-theoretic images and kernels -/

section Image

/-- The kernel of the base change of a closed immersion is the inverse image of its kernel: for
a cartesian square with `i : Z → Y` a closed immersion and `f : X → Y`, the kernel of the
projection `P → X` is `f⁻¹(ker i)`. -/
theorem ker_eq_comap_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Z}
    {f : X ⟶ Y} {i : Z ⟶ Y} [IsClosedImmersion i] (sq : IsPullback fst snd f i) :
    fst.ker = i.ker.comap f := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← sq.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- **The scheme-theoretic image of a reduced subscheme under flat base change.** For a
cartesian square `U_Y → Y`, `U_Y → U` over `g : Y → X`, `ι : U → X`, with `g` flat with reduced
base changes, and a reduced closed subscheme `Z ⊆ U`, the inverse image along `g` of the
scheme-theoretic image of `Z` is the scheme-theoretic image of `g_U⁻¹Z`. -/
theorem comap_map_eq_map_comap_of_isPullback {X Y U UY : Scheme.{u}} {ιY : UY ⟶ Y}
    {gU : UY ⟶ U} {g : Y ⟶ X} {ι : U ⟶ X} (sq : IsPullback ιY gU g ι)
    (hg : IsReducedFlatBaseChange g) (Z : U.IdealSheafData) [IsReduced Z.subscheme] :
    (Z.map ι).comap g = (Z.comap gU).map ιY := by
  have hgU : IsReducedFlatBaseChange gU := hg.of_isPullback sq
  have hZ : Z = Scheme.IdealSheafData.vanishingIdeal Z.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
  have hcl : IsClosed (gU ⁻¹' (Z.support : Set U)) := Z.support.isClosed.preimage gU.continuous
  have h1 : Z.comap gU = Scheme.IdealSheafData.vanishingIdeal ⟨_, hcl⟩ := by
    conv_lhs => rw [hZ]
    exact hgU.comap_vanishingIdeal _ _ rfl
  have hopen : IsOpenMap g := by
    have := hg.universallyOpen
    exact g.isOpenMap
  rw [h1, Scheme.IdealSheafData.map_vanishingIdeal]
  conv_lhs => rw [hZ, Scheme.IdealSheafData.map_vanishingIdeal]
  refine hg.comap_vanishingIdeal _ _ ?_
  rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure,
    hopen.preimage_closure_eq_closure_preimage g.continuous,
    ← Scheme.image_preimage_eq_of_isPullback sq.flip]
  rfl

end Image

/-! ### The extension by closure under flat base change -/

section ExtendByClosure

/-- A flat morphism with reduced base changes precomposed with an `eqToHom` is one. -/
theorem isReducedFlatBaseChange_eqToHom_comp {X Y Y' : Scheme.{u}} (e : Y' = Y) {f : Y ⟶ X}
    (hf : IsReducedFlatBaseChange f) : IsReducedFlatBaseChange (eqToHom e ≫ f) :=
  hf.of_isPullback (IsPullback.of_horiz_isIso (fst := eqToHom e) (snd := eqToHom e ≫ f) (f := f)
    (g := 𝟙 _) ⟨by simp⟩)

/-- **Blowing up along a cartesian square of flat morphisms.** Let `U_Y → Y`, `U_Y → U` over
`g : Y → X`, `ι : U → X` be a cartesian square with `g` and `ι` flat, and `Z ⊆ X` a closed
subscheme with inverse images `Z_U ⊆ U` and `Z_Y ⊆ Y`. The four canonical lifts form a
cartesian square `B_{Z_U×Y}U_Y → B_{Z_Y}Y`, `→ B_{Z_U}U` over `B_{Z_Y}Y → B_ZX`,
`B_{Z_U}U → B_ZX`. -/
theorem isPullback_canonicalLift_of_isPullback {X Y U UY : Scheme.{u}} {ιY : UY ⟶ Y}
    {gU : UY ⟶ U} {g : Y ⟶ X} {ι : U ⟶ X} (sq : IsPullback ιY gU g ι) [Flat g] [Flat ι]
    (Z : X.IdealSheafData) (ZU : U.IdealSheafData) (eU : Z.comap ι = ZU)
    (ZY : Y.IdealSheafData) (eY : Z.comap g = ZY) (e : ZY.comap ιY = ZU.comap gU) :
    IsPullback (eqToHom (congrArg blowUp e.symm) ≫ canonicalLift ιY ZY) (canonicalLift gU ZU)
      (eqToHom (congrArg blowUp eY.symm) ≫ canonicalLift g Z)
      (eqToHom (congrArg blowUp eU.symm) ≫ canonicalLift ι Z) := by
  subst eU eY
  simp only [eqToHom_refl, Category.id_comp]
  have : Flat gU := MorphismProperty.of_isPullback (P := @Flat) sq ‹_›
  have outer := (isPullback_canonicalLift_of_flat gU (Z.comap ι)).paste_horiz sq
  have e1 : (eqToHom (congrArg blowUp e.symm) ≫ canonicalLift ιY (Z.comap g)) ≫
      blowUpToBase (Z.comap g) = blowUpToBase ((Z.comap ι).comap gU) ≫ ιY := by
    rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
      eqToHom_comp_blowUpToBase e.symm]
  have e2 : canonicalLift ι Z ≫ blowUpToBase Z = blowUpToBase (Z.comap ι) ≫ ι :=
    canonicalLift_comp_blowUpToBase ι Z
  rw [← e1, ← e2] at outer
  refine IsPullback.of_right outer ?_ (isPullback_canonicalLift_of_flat g Z)
  rw [Category.assoc, canonicalLift_comp_canonicalLift, canonicalLift_comp_canonicalLift,
    canonicalLift_congr sq.w Z]
  simp

/-- **The extension by closure commutes with flat base change.** Let `U_Y → Y`, `U_Y → U` over
`g : Y → X`, `ι : U → X` be a cartesian square with `ι` (hence `U_Y → Y`) a quasi-compact open
immersion and `g` flat with reduced base changes, and let `𝐁` be a blow-up sequence starting with
`U` with reduced centres. Then the pull-back along `g` of the extension by closure of `𝐁` along
`ι` is the extension by closure of `g_U^*𝐁` along `U_Y → Y`. -/
theorem extendByClosure_pullback {U : Scheme.{u}} (B : ClosedBlowupSequence U)
    (hB : B.HasReducedCentres) : ∀ {X Y UY : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
      [QuasiCompact ι] (g : Y ⟶ X) (hg : IsReducedFlatBaseChange g) (ιY : UY ⟶ Y)
      [IsOpenImmersion ιY] [QuasiCompact ιY] (gU : UY ⟶ U) (sq : IsPullback ιY gU g ι),
      (B.extendByClosure ι).pullback g = (B.pullback gU).extendByClosure ιY := by
  induction B with
  | nil U => intros; rfl
  | cons Z B ih =>
    intro X Y UY ι _ _ g hg ιY _ _ gU sq
    have := hB.1
    have := hg.flat
    have hc := comap_map_eq_of_isOpenImmersion ι Z
    have eY := comap_map_eq_map_comap_of_isPullback sq hg Z
    have hcY := comap_map_eq_of_isOpenImmersion ιY (Z.comap gU)
    rw [extendByClosure_cons_of_comap_map_eq Z B ι hc]
    change cons _ _ = (cons (Z.comap gU) (B.pullback (canonicalLift gU Z))).extendByClosure ιY
    rw [extendByClosure_cons_of_comap_map_eq _ _ ιY hcY]
    refine cons_eq_cons_iff.2 ⟨eY, ?_⟩
    have sq' := isPullback_canonicalLift_of_isPullback sq (Z.map ι) Z hc _ eY hcY
    have hg1 := isReducedFlatBaseChange_eqToHom_comp (congrArg blowUp eY.symm)
      (hg.canonicalLift (Z.map ι))
    have : IsOpenImmersion (canonicalLift ι (Z.map ι)) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (isPullback_canonicalLift_of_flat ι (Z.map ι)) ‹_›
    have : QuasiCompact (canonicalLift ι (Z.map ι)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (isPullback_canonicalLift_of_flat ι (Z.map ι)) ‹_›
    have : IsOpenImmersion (canonicalLift ιY ((Z.comap gU).map ιY)) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (isPullback_canonicalLift_of_flat ιY ((Z.comap gU).map ιY)) ‹_›
    have : QuasiCompact (canonicalLift ιY ((Z.comap gU).map ιY)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (isPullback_canonicalLift_of_flat ιY ((Z.comap gU).map ιY)) ‹_›
    have key := ih hB.2 _ _ hg1 _ _ sq'
    exact (pullback_eqToHom_comp_heq _ _ _).symm.trans (heq_of_eq key)

end ExtendByClosure

/-! ### Restriction under flat base change -/

section Restriction

/-- The projection `γ : g⁻¹H → H` of the inverse image of a closed subscheme. -/
noncomputable def comapSubschemeProj {X Y : Scheme.{u}} (g : Y ⟶ X) (H : X.IdealSheafData) :
    (H.comap g).subscheme ⟶ H.subscheme :=
  (H.comapIso g).hom ≫ Limits.pullback.snd g H.subschemeι

/-- `g⁻¹H` is the fibre product `Y ×_X H`. -/
theorem isPullback_comapSubschemeProj {X Y : Scheme.{u}} (g : Y ⟶ X) (H : X.IdealSheafData) :
    IsPullback (H.comap g).subschemeι (comapSubschemeProj g H) g H.subschemeι :=
  IsPullback.of_iso_pullback ⟨by
    rw [comapSubschemeProj, Category.assoc, ← Limits.pullback.condition,
      ← Scheme.IdealSheafData.comapIso_hom_fst_assoc]⟩ (H.comapIso g)
    (Scheme.IdealSheafData.comapIso_hom_fst H g) rfl

/-- Given equal pairs `⟨C, iY ≫ ρ⟩ = ⟨C', c ≫ i⟩` over a cartesian square, the square formed by
`iY`, `c`, `ρ` and `i` is cartesian. -/
theorem isPullback_of_sigma_eq {X Y H HY X' Y' T : Scheme.{u}} {π : X' ⟶ X} {πY : Y' ⟶ Y}
    {ρ : Y' ⟶ X'} {g : Y ⟶ X} (hB : IsPullback πY ρ g π) (ιY : HY ⟶ Y) (ι : H ⟶ X)
    {C C' : ClosedBlowupSequence HY} (hC : C = C') (iY : C.target ⟶ Y') (c : C'.target ⟶ T)
    (i : T ⟶ X') (τ : T ⟶ H)
    (hp : (⟨C, iY ≫ ρ⟩ : Σ D : ClosedBlowupSequence HY, D.target ⟶ X') = ⟨C', c ≫ i⟩)
    (hiY : iY ≫ πY = C.toBase ≫ ιY) (hi : i ≫ π = τ ≫ ι)
    (s : IsPullback (C'.toBase ≫ ιY) c g (τ ≫ ι)) :
    IsPullback iY (eqToHom (congrArg target hC) ≫ c) ρ i := by
  subst hC
  simp only [eqToHom_refl, Category.id_comp]
  have hp' : iY ≫ ρ = c ≫ i := eq_of_heq (Sigma.mk.inj hp).2
  rw [← hiY, ← hi] at s
  exact IsPullback.of_right s hp' hB

/-- **Restriction to a closed subscheme commutes with flat base change.** For a blow-up sequence
`𝐁` starting with `X`, a closed subscheme `H ⊆ X` and a flat `g : Y → X`, the restriction of
`g^*𝐁` to `g⁻¹H` is the pull-back of `𝐁|_H` along `γ : g⁻¹H → H`, and under this identification
the square formed by `j_Y : (g^*𝐁)|_{g⁻¹H} → Y_r`, `j : 𝐁|_H → X_r` and the last morphisms of
the pull-backs is cartesian. -/
theorem isPullback_restrictHom_pullback {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (g : Y ⟶ X) [Flat g] (H : X.IdealSheafData) :
    ∃ e : ((B.pullback g).restrict (H.comap g)).target =
        ((B.restrict H).pullback (comapSubschemeProj g H)).target,
      IsPullback ((B.pullback g).restrictHom (H.comap g))
        (eqToHom e ≫ (B.restrict H).pullbackHom (comapSubschemeProj g H)) (B.pullbackHom g)
        (B.restrictHom H) := by
  have sqH := isPullback_comapSubschemeProj g H
  have hγ : Flat (comapSubschemeProj g H) := MorphismProperty.of_isPullback (P := @Flat) sqH ‹_›
  have h1 := pullback_pullback_sigma_heq B g (H.comap g).subschemeι
    ((H.comap g).subschemeι ≫ g) rfl (by simp)
  have h2 := pullback_pullback_sigma_heq B H.subschemeι (comapSubschemeProj g H)
    ((H.comap g).subschemeι ≫ g) rfl (by simp [sqH.w])
  have hp : (⟨(B.pullback g).restrict (H.comap g),
      (B.pullback g).restrictHom (H.comap g) ≫ B.pullbackHom g⟩ :
        Σ D : ClosedBlowupSequence (H.comap g).subscheme, D.target ⟶ B.target) =
      ⟨(B.restrict H).pullback (comapSubschemeProj g H),
        (B.restrict H).pullbackHom (comapSubschemeProj g H) ≫ B.restrictHom H⟩ :=
    (eq_of_heq h1).trans (eq_of_heq h2).symm
  have hC := congrArg Sigma.fst hp
  refine ⟨congrArg target hC, ?_⟩
  refine isPullback_of_sigma_eq (isPullback_pullback_toBase_of_flat B g)
    (H.comap g).subschemeι H.subschemeι hC _ _ _ (B.restrict H).toBase hp
    (pullbackHom_toBase_comm _ _) (pullbackHom_toBase_comm _ _) ?_
  exact (isPullback_pullback_toBase_of_flat (B.restrict H) (comapSubschemeProj g H)).paste_horiz
    sqH

/-- **The birational transform of a closed subscheme under flat base change** (Kollár 3.30.2):
for flat `g : Y → X`, the scheme-theoretic image of `(g^*𝐁)|_{g⁻¹H} → Y_r` is the inverse image
along `g_r : Y_r → X_r` of the scheme-theoretic image of `𝐁|_H → X_r`. -/
theorem ker_restrictHom_pullback {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (g : Y ⟶ X)
    [Flat g] (H : X.IdealSheafData) :
    ((B.pullback g).restrictHom (H.comap g)).ker =
      (B.restrictHom H).ker.comap (B.pullbackHom g) := by
  obtain ⟨_, sq⟩ := isPullback_restrictHom_pullback B g H
  have : IsClosedImmersion (B.restrictHom H) := isClosedImmersion_pullbackHom B H.subschemeι
  exact ker_eq_comap_of_isPullback sq

end Restriction

end Kollar

end MMP.Resolution
