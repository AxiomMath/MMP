module

public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial

/-!
# The order reduction functors `𝓑𝓜𝓞`, `𝓑𝓓` and `𝓑𝓞` (Kollár, *Resolution*, 3.70, 3.102–3.111)

Kollár proves Theorems 3.68 and 3.69 together by induction on the dimension (3.70). An
*unmarked family* `𝓑 = (𝓑_{d,μ})` assigns blow-up sequences to triples, a *marked family*
`𝓜 = (𝓜_{d,μ})` to marked triples; they are *order-reduction families* on dimensions `a, …, b`
when every `𝓑_μ` (resp. `𝓜_μ`) is an order reduction functor there. From an unmarked family the
functor `𝓑𝓜𝓞` reduces the order of a marked ideal `(I, m)` in three steps (3.111): it reduces the
nonmonomial part `N(I)`, then the ideals `K_s(I, m) = N(I)^m + I^s`, and finally the monomial part
by the monomial order reduction. From a marked family in lower dimensions the functor `𝓑𝓓`
separates `I` from a divisor `E^j` by restricting the well-tuned coefficient ideal to `E^j`
(Lemma 3.102), `𝓑𝓞^H` reduces the order in the presence of a hypersurface of maximal contact `H`
(Thm. 3.103, 3.104), `𝓑_{n,m}` does so for local triples having an MC-hypersurface, and `𝓑𝓞_{n,m}`
glues these along open covers. Recursion on `n` gives the canonical families (3.70).

## Main definitions

* `MMP.Resolution.UnmarkedFamily`, `MMP.Resolution.MarkedFamily`,
  `MMP.Resolution.IsOrderReductionFamily`, `MMP.Resolution.IsMarkedOrderReductionFamily`.
* `MMP.Resolution.bmoStepOne`, `MMP.Resolution.bmoStepTwo`, `MMP.Resolution.bmoFunctor`.
* `MMP.Resolution.bdFunctor`, `MMP.Resolution.divisorSeparationSequence`,
  `MMP.Resolution.boMaximalContact`.
* `MMP.Resolution.mcLocalTriples`, `MMP.Resolution.boLocal`, `MMP.Resolution.boFunctor`.
* `MMP.Resolution.boFamily`, `MMP.Resolution.bmoFamily`.

## Implementation notes

Families are total: `𝓑_{d,μ}` and `𝓜_{d,μ}` assign a blow-up sequence to every triple
(resp. marked triple); only their values on triples of dimension `d` (and maximal order `≤ μ`,
resp. marking `μ`) matter, and the order-reduction conditions only concern these. Likewise the
functors of this file are defined on all triples, their values outside the source's domain
being junk (mostly the empty sequence). The index `j` of `𝓑𝓓_{n,m,j}` is `0`-based: `j = 0` is
Kollár's `E^1` (and `E^0 := H` in `𝓑𝓞^H`).

Along a blow-up sequence starting with `(X, I, m, E)` (resp. `(X, I, E)`), the end is computed
with the marked transforms (resp. the controlled transforms) of the ideal and the total transforms
of the ordered divisor (`MarkedTriple.endOf`, `FieldBlowupTriple.endOf`), over `k` by
`X_r → X → Spec k`.

The push-forward `τ_*𝐁` of 3.30.3 is characterized by `ClosedBlowupSequence.IsPushforward`, which
determines it; `ClosedBlowupSequence.pushforward` picks it (the empty sequence if there is none).
The birational transform `H'` of `H` along a blow-up sequence is the scheme-theoretic image of the
last morphism of its restriction to `H`. The restriction `A(I_2)|_U` of the monomial part to the
open `U = X_2 ∖ cosupp N(I_2)` is the monomial part of `I_2|_U` with respect to `E_2|_U` (orders
along prime divisors are local at their generic points). The well-tuned ideal of 3.103 is
`W(I) = W_{m!}(I)`; the MC-hypersurface `H(X, I)` is chosen by choice (`⊤`, the empty subscheme,
when there is none).

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.68–3.70, 3.98–3.111]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Families of blow-up sequence functors -/

/-- An *unmarked family* `𝓑 = (𝓑_{d,μ})_{d, μ}`: for every dimension `d` and order `μ`, an
assignment of a blow-up sequence starting with `X` to triples `(X, I, E)` (relevant for
`dim X = d` and `maxord I ≤ μ`). -/
abbrev UnmarkedFamily : Type (u + 1) :=
  ℕ → ℕ → (t : FieldBlowupTriple.{u}) → ClosedBlowupSequence t.X

/-- A *marked family* `𝓜 = (𝓜_{d,μ})_{d, μ}`: for every dimension `d` and marking `μ`, an
assignment of a blow-up sequence starting with `X` to marked triples `(S, J, μ, E_S)` (relevant
for `dim S = d`). -/
abbrev MarkedFamily : Type (u + 1) :=
  ℕ → ℕ → (t : MarkedTriple.{u}) → ClosedBlowupSequence t.X

/-- An unmarked family `𝓑` is an *order-reduction family on dimensions `a, …, b`* (Kollár
Thm. 3.68 restricted to dimensions `a, …, b`): for every `μ ≥ 1` the assignment
`𝓑_μ : (X, I, E) ↦ 𝓑_{dim X, μ}(X, I, E)` on the class `𝒯_{μ,[a,b]}` of triples with
`a ≤ dim X ≤ b` and `maxord I ≤ μ` is (1) a smooth blow-up sequence functor of order `μ` whose
last ideal `I_r` has `maxord I_r < μ`, (2a) commutes with smooth morphisms between members of
`𝒯_{μ,[a,b]}` and (2b) commutes with change of fields. -/
@[mmp "def_kr3e_order_reduction_family"]
def IsOrderReductionFamily (a b : ℕ) (B : UnmarkedFamily.{u}) : Prop :=
  ∀ μ : ℕ, 1 ≤ μ → ∃ F : OrderBlowupSequenceFunctor.{u} μ (idealTriplesOfDim (Set.Icc a b) μ),
    (∀ t ht, F.toFun t ht = B (dimNat t.X) μ t) ∧ IsOrderReductionFunctorIdeals μ _ F

/-- A marked family `𝓜` is a *marked order-reduction family on dimensions `a, …, b`* (Kollár
Thm. 3.69 restricted to dimensions `a, …, b`): for every `μ ≥ 1` the assignment
`𝓜_μ : (S, J, μ, E_S) ↦ 𝓜_{dim S, μ}(S, J, μ, E_S)` on the class `𝒯^mk_{μ,[a,b]}` of marked
triples with marking `μ` and `a ≤ dim S ≤ b` is (1) a smooth blow-up sequence functor of order
`≥ μ` whose last ideal `J_r` has `maxord J_r < μ`, (2a) commutes with smooth morphisms between
members of `𝒯^mk_{μ,[a,b]}` and (2b) commutes with change of fields. -/
@[mmp "def_kr3e_marked_order_reduction_family"]
def IsMarkedOrderReductionFamily (a b : ℕ) (M : MarkedFamily.{u}) : Prop :=
  ∀ μ : ℕ, 1 ≤ μ →
    ∃ F : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim (Set.Icc a b) μ),
      (∀ t ht, F.toFun t ht = M (dimNat t.X) μ t) ∧ IsOrderReductionFunctorMarked μ _ F

/-! ### Ends of blow-up sequences -/

/-- The end `(X_r, I_r, m, E_r)` of a blow-up sequence regarded as a sequence starting with the
marked triple `(X, I, m, E)`: `(I_r, m) = Π⁻¹_*(I, m)` and `E_r` the total transform. -/
def MarkedTriple.endOf (t : MarkedTriple.{u}) (m : ℕ) (B : ClosedBlowupSequence t.X) :
    MarkedTriple.{u} :=
  ⟨⟨⟨B.target, (B.markedTransform ⟨t.I, m⟩).I, B.orderedTotalTransform t.E⟩, t.k,
    B.toBase ≫ t.sX⟩, m⟩

/-- The end `(X_r, I_r, E_r)` of a blow-up sequence regarded as a sequence starting with the
triple `(X, I, E)` (Kollár Def. 3.66): `I_r` the controlled transform and `E_r` the total
transform. -/
def FieldBlowupTriple.endOf (t : FieldBlowupTriple.{u}) (B : ClosedBlowupSequence t.X) :
    FieldBlowupTriple.{u} :=
  ⟨⟨B.target, B.controlledTransform t.I, B.orderedTotalTransform t.E⟩, t.k, B.toBase ≫ t.sX⟩

/-! ### The functor `𝓑𝓜𝓞` -/

section BMO

variable (B : UnmarkedFamily.{u}) (d m : ℕ)

open Classical in
/-- `S_1^{(q)}(X, I, m, E)` (Kollár 3.111, Step 1): `S_1^{(0)}` is empty; `S_1^{(q+1)}` is empty if
`μ = maxord N(I) < m`, and otherwise `𝐁 = 𝓑_{d,μ}(X, N(I), E)` followed by `S_1^{(q)}` of its end
`(X', I', m, E')` if this is a marked triple (and by the empty sequence otherwise). -/
@[mmp "def_kr3e_bmo_step_one"]
def bmoStepOneAux : ℕ → (t : MarkedTriple.{u}) → ClosedBlowupSequence t.X
  | 0, t => .nil t.X
  | q + 1, t =>
    if maxOrder (nonmonomialPart t.I t.E) < m then .nil t.X
    else
      let S := B d (maxOrder (nonmonomialPart t.I t.E)).toNat
        ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩
      S.append (if t.endOf m S ∈ markedTriples then bmoStepOneAux q (t.endOf m S) else .nil _)

/-- The *Step-1 sequence* `S_1^{(μ_0+1)}(X, I, m, E)`, `μ_0 = maxord N(I)` (Kollár 3.111,
Step 1). -/
@[mmp "def_kr3e_bmo_step_one"]
def bmoStepOne (t : MarkedTriple.{u}) : ClosedBlowupSequence t.X :=
  bmoStepOneAux B d m ((maxOrder (nonmonomialPart t.I t.E)).toNat + 1) t

/-- `s(X, I) = maxord_{cosupp(I, m)} N(I)`, `0` if `cosupp(I, m) = ∅` (Kollár 3.111, Step 2). -/
@[mmp "def_kr3e_bmo_step_two"]
def bmoStepTwoOrder (t : MarkedTriple.{u}) : ℕ :=
  (maxOrderAlong (nonmonomialPart t.I t.E) (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport).toNat

open Classical in
/-- `S_2^{(q)}(X, I, m, E)` (Kollár 3.111, Step 2): `S_2^{(0)}` is empty; `S_2^{(q+1)}` is empty if
`s = s(X, I) = 0`, and otherwise `𝓑_{d,ms}(X, K_s(I, m), E)` followed by `S_2^{(q)}` of its end if
this is a marked triple (and by the empty sequence otherwise). -/
@[mmp "def_kr3e_bmo_step_two"]
def bmoStepTwoAux : ℕ → (t : MarkedTriple.{u}) → ClosedBlowupSequence t.X
  | 0, t => .nil t.X
  | q + 1, t =>
    if bmoStepTwoOrder m t = 0 then .nil t.X
    else
      let S := B d (m * bmoStepTwoOrder m t)
        ⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩
      S.append (if t.endOf m S ∈ markedTriples then bmoStepTwoAux q (t.endOf m S) else .nil _)

/-- The *Step-2 sequence* `S_2^{(s_0+1)}(X, I, m, E)`, `s_0 = s(X, I)` (Kollár 3.111, Step 2). -/
@[mmp "def_kr3e_bmo_step_two"]
def bmoStepTwo (t : MarkedTriple.{u}) : ClosedBlowupSequence t.X :=
  bmoStepTwoAux B d m (bmoStepTwoOrder m t + 1) t

open Classical in
/-- The functor `𝓑𝓜𝓞_{d,m}[𝓑]` (Kollár 3.111, proof of 3.107, Steps 1–3): for a marked triple
`(X, I, m, E)` with `dim X = d`, the Step-1 sequence `S_1` with end `(X_1, I_1, m, E_1)`, followed
by the Step-2 sequence `S_2` of `(X_1, I_1, m, E_1)` with end `(X_2, I_2, m, E_2)` (each empty if
its input is not a marked triple), followed by the extension by closure to `X_2` of the monomial
order reduction sequence of `(U, E_2|_U, A(I_2)|_U, m)`, `U = X_2 ∖ cosupp N(I_2)`, with empty
blow-ups deleted. -/
@[mmp "def_kr3e_bmo_functor"]
def bmoFunctor (t : MarkedTriple.{u}) : ClosedBlowupSequence t.X :=
  let S₁ := if t ∈ markedTriples then bmoStepOne B d m t else .nil t.X
  let t₁ := t.endOf m S₁
  let S₂ := if t₁ ∈ markedTriples then bmoStepTwo B d m t₁ else .nil t₁.X
  let t₂ := t₁.endOf m S₂
  let U : t₂.X.Opens := (nonmonomialPart t₂.I t₂.E).support.compl
  let C : MonomialData U :=
    ⟨t₂.k, U.ι ≫ t₂.sX, t₂.E.comap U.ι, monomialPartCoeff (t₂.I.comap U.ι) (t₂.E.comap U.ι)⟩
  (S₁.append (S₂.append ((C.monomialOrderReduction m).extendByClosure U.ι))).reduction

end BMO

/-! ### The functor `𝓑𝓓` and the divisor separation sequence -/

namespace ClosedBlowupSequence

open Classical in
/-- The push-forward `j_*𝐁(S)` of a blow-up sequence along `j : S → X` (Kollár 3.30.3), the
blow-up sequence `𝐁^X` with `ClosedBlowupSequence.IsPushforward j 𝐁(S) 𝐁^X` (the empty sequence if
there is none). -/
def pushforward {S X : Scheme.{u}} (j : S ⟶ X) (B : ClosedBlowupSequence S) :
    ClosedBlowupSequence X :=
  if h : ∃ B', IsPushforward j B B' then h.choose else nil X

end ClosedBlowupSequence

/-- The ordered divisor `(E^i)_{i ≠ j}` obtained by deleting the `j`-th entry (`0`-based), the
others ordered as in `E`. -/
def OrderedDivisor.deleteIndex {X : Scheme.{u}} (E : OrderedDivisor X) (j : ℕ) :
    OrderedDivisor X :=
  let L := (List.finRange E.s).filter fun i : Fin E.s => i.val ≠ j
  ⟨L.length, fun i => E.E (L.get i)⟩

section BD

variable (M : MarkedFamily.{u}) (n m : ℕ)

open Classical in
/-- The functor `𝓑𝓓_{n,m,j}` (Kollár Lemma 3.102 and its proof), `j` the `0`-based index of
`E^{j+1}`: for a triple `(X, I, E)` with `dim X = n`, the empty sequence if `maxord I ≠ m`; if
`maxord I = m`, with `μ = m!`, `W = W_μ(I)` and `Z_{-1} = Z_{-1}(W, μ, E^j)`, the (trivial)
blow-up `π_{-1} : X_0 = B_{Z_{-1}}X → X` followed by the push-forward along the inclusion
`τ : S = E^j ↪ X_0` of `𝐁_S = 𝓜_{n-1,μ}(S, W_0𝒪_S, μ, E_S)`, `W_0 = 𝒪(μZ_{-1})·W` the birational
transform of `(W, μ)`, `E_S = (E^i ∩ S)_{i ≠ j}` (`𝐁_S` empty if `S = ∅` or this is not a marked
triple), with empty blow-ups deleted. -/
@[mmp "def_kr3e_bd_functor"]
def bdFunctor (j : ℕ) (t : FieldBlowupTriple.{u}) : ClosedBlowupSequence t.X :=
  if h : maxOrder t.I = m ∧ j < t.E.s then
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, h.2⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, h.2⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ, ((t.E.comap π).deleteIndex j).comap τ⟩,
        t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    let BS : ClosedBlowupSequence S.subscheme :=
      if (S.support : Set (blowUp Z)).Nonempty ∧ tS ∈ markedTriples then M (n - 1) μ tS
      else .nil _
    (ClosedBlowupSequence.cons Z (BS.pushforward τ)).reduction
  else .nil t.X

open Classical in
/-- `Π_{(j)}`, the first `j` steps of the divisor separation sequence of `(X, I, E)`, `n = dim X`:
`Π_{(0)}` is empty, and `Π_{(j+1)}` is `Π_{(j)}` followed by `𝓑𝓓_{n,m,j}` of its end
`(X_{(j)}, I_{(j)}, E_{(j)})` if that is a triple, and `Π_{(j)}` otherwise. -/
@[mmp "def_kr3e_divisor_separation_sequence"]
def divisorSeparationAux (t : FieldBlowupTriple.{u}) : ℕ → ClosedBlowupSequence t.X
  | 0 => .nil t.X
  | j + 1 =>
    let P := divisorSeparationAux t j
    if IsTriple (t.endOf P).sX (t.endOf P).I (t.endOf P).E then
      P.append (bdFunctor M (dimNat t.X) m j (t.endOf P))
    else P

/-- The *divisor separation sequence* `Π_{(s)}` of a triple `(X, I, E)`, `E = (E^1, …, E^s)`
(Kollár 3.104 Step 2.1 and Step 2.1.`j`; Thm. 3.103 proof, Step 2.1). -/
@[mmp "def_kr3e_divisor_separation_sequence"]
def divisorSeparationSequence (t : FieldBlowupTriple.{u}) : ClosedBlowupSequence t.X :=
  divisorSeparationAux M m t t.E.s

open Classical in
/-- The functor `𝓑𝓞^H_m` (Kollár Thm. 3.103 proof Steps 1–2 and 3.104 Steps 2.1–2.2): for a
triple `(X, J, E)` with `maxord J = m`, `E = (E^1, …, E^s)`, and a smooth hypersurface `H`, the
divisor separation sequence `Π_sep` with end `(X', J', E')`, followed by the extension by closure
to `X'` of `𝐁_V = 𝓑𝓓_{dim X, m, 1}(V, J'|_V, E^V)`, where `V = X' ∖ ⋃_{i ≤ s} E'^i`,
`E^V = (H' ∩ V, E'^{s+1} ∩ V, …, E'^{s'} ∩ V)`, `H'` the birational transform of `H` (`𝐁_V` empty
if `V = ∅` or `(V, J'|_V, E^V)` is not a triple), with empty blow-ups deleted. -/
@[mmp "def_kr3e_bo_maximal_contact_case"]
def boMaximalContact (t : FieldBlowupTriple.{u}) (H : t.X.IdealSheafData) :
    ClosedBlowupSequence t.X :=
  let P := divisorSeparationSequence M m t
  let t' := t.endOf P
  let H' : t'.X.IdealSheafData := (P.restrictHom H).ker
  let V : t'.X.Opens :=
    (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
  let EV : OrderedDivisor V :=
    ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
      fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩
  let tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, EV⟩, t'.k, V.ι ≫ t'.sX⟩
  let BV : ClosedBlowupSequence V :=
    if (V : Set t'.X).Nonempty ∧ IsTriple tV.sX tV.I tV.E then bdFunctor M (dimNat t.X) m 0 tV
    else .nil _
  (P.append (BV.extendByClosure V.ι)).reduction

end BD

/-! ### Local triples and the functor `𝓑𝓞` -/

/-- The class `𝓛𝓣_{n,m}` of local triples (Kollár Thm. 3.103 proof, Steps 2–3): triples
`(X, I, E)` with `dim X = n` and `maxord I ≤ m` such that either `maxord I < m`, or `maxord I = m`
and `I` has an MC-hypersurface. -/
@[mmp "def_kr3e_mc_local_triple"]
def mcLocalTriples (n m : ℕ) : Set FieldBlowupTriple.{u} :=
  {t | t ∈ triples ∧ HasDimensionIn t.X {n} ∧ maxOrder t.I ≤ m ∧
    (maxOrder t.I < m ∨ (maxOrder t.I = m ∧ ∃ H, IsMCHypersurface t.sX t.I H))}

section BO

variable (M : MarkedFamily.{u})

open Classical in
/-- The MC-hypersurface `H(X, I)` for `I`, chosen once and for all (`⊤`, the empty subscheme, if
there is none). -/
@[mmp "def_kr3e_bo_local"]
def mcHypersurfaceChoice (t : FieldBlowupTriple.{u}) : t.X.IdealSheafData :=
  if h : ∃ H, IsMCHypersurface t.sX t.I H then h.choose else ⊤

open Classical in
/-- The functor `𝓑_{n,m}` on local triples (Kollár Thm. 3.103 proof, Steps 1–2): for
`(X, I, E) ∈ 𝓛𝓣_{n,m}`, the empty sequence if `maxord I < m`, and otherwise
`𝓑𝓞^H_{m!}(X, W(I), E)` with `W(I)` the well-tuned ideal and `H = H(X, I)` an MC-hypersurface for
`I`. -/
@[mmp "def_kr3e_bo_local"]
def boLocal (m : ℕ) (t : FieldBlowupTriple.{u}) : ClosedBlowupSequence t.X :=
  if maxOrder t.I < m then .nil t.X
  else boMaximalContact M m.factorial ⟨⟨t.X, wellTunedIdeal t.sX t.I, t.E⟩, t.k, t.sX⟩
    (mcHypersurfaceChoice t)

open Classical in
/-- The functor `𝓑𝓞_{n,m}` (Kollár Thm. 3.103 proof, Step 3, global case): for a triple
`(X, I, E)` with `dim X = n` and `maxord I ≤ m`, a blow-up sequence `𝐁` starting with `X` (chosen
by choice) such that `g^*𝐁 = 𝓑_{n,m}(X^*, g^*I, g⁻¹E)` for every surjective open cover map
`g : X^* → X` with `(X^*, g^*I, g⁻¹E) ∈ 𝓛𝓣_{n,m}`, if there is one, and the empty sequence
otherwise. -/
@[mmp "def_kr3e_bo_functor"]
def boFunctor (n m : ℕ) (t : FieldBlowupTriple.{u}) : ClosedBlowupSequence t.X :=
  if h : ∃ B : ClosedBlowupSequence t.X, ∀ (X' : Scheme.{u}) (g : X' ⟶ t.X), IsOpenCoverMap g →
      Surjective g → t.pullback g ∈ mcLocalTriples n m → B.pullback g = boLocal M m (t.pullback g)
  then h.choose else .nil t.X

end BO

/-! ### The canonical families -/

/-- The truncation `(𝓑_{d,ν})_{d ≤ n}` of an unmarked family (empty sequences in dimensions
`> n`). -/
def UnmarkedFamily.truncate (F : UnmarkedFamily.{u}) (n : ℕ) : UnmarkedFamily.{u} :=
  fun d ν t => if d ≤ n then F d ν t else .nil t.X

/-- The marked family `(𝓑𝓜𝓞_{d,ν}[(𝓑_{e,ν'})_{e ≤ d}])_{d ≤ n}` built from an unmarked family
(empty sequences in dimensions `> n`). -/
def bmoFamilyOf (F : UnmarkedFamily.{u}) (n : ℕ) : MarkedFamily.{u} :=
  fun d ν t => if d ≤ n then bmoFunctor (F.truncate d) d ν t else .nil t.X

/-- The families `(𝓑𝓞_{d,μ})_{d ≤ n}` of Kollár 3.70 (empty sequences in dimensions `> n`):
`𝓑𝓞_{0,μ}` is empty, and `𝓑𝓞_{n+1,μ}` is the functor `𝓑𝓞_{n+1,μ}` built from the marked family
`(𝓑𝓜𝓞_{d,ν})_{d ≤ n}`. -/
@[mmp "def_kr3e_order_reduction_families"]
def boFamilyUpTo : ℕ → UnmarkedFamily.{u}
  | 0 => fun _ _ t => .nil t.X
  | n + 1 => fun d μ t =>
    if d ≤ n then boFamilyUpTo n d μ t
    else if d = n + 1 then boFunctor (bmoFamilyOf (boFamilyUpTo n) n) (n + 1) μ t
    else .nil t.X

/-- The canonical family `𝓑𝓞_{n,μ}` (Kollár 3.70): defined by recursion on `n`, `𝓑𝓞_{0,μ}`
assigning the empty sequence to every triple, and for `n ≥ 1`, `𝓑𝓞_{n,μ}` the functor
`𝓑𝓞_{n,μ}` of Kollár 3.103 built from the marked family `(𝓑𝓜𝓞_{d,ν})_{d ≤ n-1}` (with `N = n`). -/
@[mmp "def_kr3e_order_reduction_families"]
def boFamily : UnmarkedFamily.{u} :=
  fun n => boFamilyUpTo n n

/-- The canonical family `𝓑𝓜𝓞_{n,μ} = 𝓑𝓜𝓞_{n,μ}[(𝓑𝓞_{d,ν})_{d ≤ n}]` (Kollár 3.70). -/
@[mmp "def_kr3e_order_reduction_families"]
def bmoFamily : MarkedFamily.{u} :=
  fun n => bmoFunctor ((boFamilyUpTo n).truncate n) n

/-- The truncations agree: `𝓑𝓞_{d,μ}` computed at stage `n ≥ d` is `𝓑𝓞_{d,μ}`. -/
@[mmp "def_kr3e_order_reduction_families"]
theorem boFamilyUpTo_of_le {d n : ℕ} (h : d ≤ n) : boFamilyUpTo.{u} n d = boFamily.{u} d := by
  induction n with
  | zero => obtain rfl : d = 0 := by omega
            rfl
  | succ n ih =>
    rcases Nat.lt_or_ge n d with hd | hd
    · obtain rfl : d = n + 1 := by omega
      rfl
    · funext μ t
      simp only [boFamilyUpTo, hd, ↓reduceIte]
      exact congrFun (congrFun (ih hd) μ) t

end MMP.Resolution
