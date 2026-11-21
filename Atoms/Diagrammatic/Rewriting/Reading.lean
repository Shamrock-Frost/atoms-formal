import Atoms.Diagrammatic.Rewriting.Chain
import Atoms.ForMathlib.CategoryTheory.Bicategory.Structural

open CategoryTheory Bicategory FreeBicategory

universe w v u v'

namespace Atoms.Diagrammatic.Layered

namespace Signature

variable (S : Signature.{v'})

def GenQuiver : Type v' := S.Pt

instance : Quiver S.GenQuiver where
  Hom x y := {e : S.Ed // S.edgeSource e = x ∧ S.edgeTarget e = y}

def PathQuiver : Type v' := S.Pt

instance : Quiver S.PathQuiver where
  Hom x y := {e : Edge S.Pt S.Ed // S.src e = x ∧ S.tgt e = y}

def freePrefunctor : Prefunctor S.PathQuiver (FreeBicategory S.GenQuiver) where
  obj x := (x : S.Pt)
  map {x y} (e : {e : Edge S.Pt S.Ed // S.src e = x ∧ S.tgt e = y}) := match e with
    | ⟨.gen g, h⟩ => Hom.of (B := S.GenQuiver) ⟨g, h⟩
    | ⟨.unit z, h⟩ => Quiver.homOfEq (V := FreeBicategory S.GenQuiver)
        (Hom.id (B := S.GenQuiver) z) h.1 h.2

def mkPrefunctor {V : Type u} [Quiver.{v} V] (obj : S.Pt → V)
    (map : (e : S.Ed) → obj (S.edgeSource e) ⟶ obj (S.edgeTarget e)) :
    Prefunctor S.GenQuiver V where
  obj := obj
  map {_ _} (e : {e : S.Ed // S.edgeSource e = _ ∧ S.edgeTarget e = _}) :=
    Quiver.homOfEq (map e.1) (congrArg obj e.2.1) (congrArg obj e.2.2)

variable [DecidableEq S.Pt]

def toPath : (p : List (Edge S.Pt S.Ed)) → {x y : S.Pt} → S.walk x p = some y →
    Quiver.Path (V := S.PathQuiver) x y
  | [], _, _, h => Quiver.Path.cast rfl (Option.some.inj h) .nil
  | e :: p, x, _, h => (Quiver.Hom.toPath (V := S.PathQuiver) (a := x) (b := S.tgt e)
      (⟨e, (S.walk_cons_eq_some.1 h).1, rfl⟩ : {e' : Edge S.Pt S.Ed // S.src e' = x ∧
        S.tgt e' = S.tgt e})).comp (toPath p (S.walk_cons_eq_some.1 h).2)

theorem toPath_congr {p p' : List (Edge S.Pt S.Ed)} (e : p = p') {x y : S.Pt}
    (h : S.walk x p = some y) (h' : S.walk x p' = some y) : S.toPath p h = S.toPath p' h' := by
  subst e
  rfl

theorem toPath_append : ∀ {p q : List (Edge S.Pt S.Ed)} {x y z : S.Pt}
    (hpq : S.walk x (p ++ q) = some z) (hp : S.walk x p = some y) (hq : S.walk y q = some z),
    S.toPath (p ++ q) hpq = (S.toPath p hp).comp (S.toPath q hq)
  | [], q, x, y, z, hpq, hp, hq => by
    obtain rfl : x = y := Option.some.inj hp
    exact (Quiver.Path.nil_comp _).symm
  | e :: p, q, x, y, z, hpq, hp, hq => by
    have ih := toPath_append (S.walk_cons_eq_some.1 hpq).2 (S.walk_cons_eq_some.1 hp).2 hq
    exact (congrArg _ ih).trans (Quiver.Path.comp_assoc _ _ _).symm

theorem walk_of_pathEnds {p : List (Edge S.Pt S.Ed)} {x y : S.Pt}
    (h : S.pathEnds p = some (x, y)) : S.walk x p = some y :=
  (S.pathEnds_eq_some_iff.1 h).2

theorem walk_append₃ {L s R : List (Edge S.Pt S.Ed)} {x m n y : S.Pt} (hL : S.walk x L = some m)
    (hs : S.walk m s = some n) (hR : S.walk n R = some y) : S.walk x (L ++ s ++ R) = some y := by
  rw [walk_append, walk_append, hL, Option.bind_some, hs, Option.bind_some, hR]

theorem walk_split {L s R : List (Edge S.Pt S.Ed)} {x y : S.Pt}
    (h : S.walk x (L ++ s ++ R) = some y) (hs : (S.pathEnds s).isSome) :
    S.walk x L = some ((S.pathEnds s).get hs).1 ∧
      S.walk ((S.pathEnds s).get hs).1 s = some ((S.pathEnds s).get hs).2 ∧
        S.walk ((S.pathEnds s).get hs).2 R = some y := by
  have hE : S.pathEnds s = some ((S.pathEnds s).get hs) := (Option.some_get hs).symm
  generalize (S.pathEnds s).get hs = E at hE ⊢
  rw [walk_append, walk_append] at h
  obtain ⟨b, hb, hR⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a, ha, hab⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨hne, hmn⟩ := S.pathEnds_eq_some_iff.1 hE
  obtain _ | ⟨e, s⟩ := s
  · exact absurd rfl hne
  obtain ⟨rfl, -⟩ := S.walk_cons_eq_some.1 hab
  obtain ⟨hm, -⟩ := S.pathEnds_cons_eq_some.1 hE
  rw [← hm] at hmn ⊢
  obtain rfl : b = E.2 := Option.some.inj (hab.symm.trans hmn)
  exact ⟨ha, hmn, hR⟩

theorem toPath_append₃ {p L s R : List (Edge S.Pt S.Ed)} (e : L ++ s ++ R = p) {x m n y : S.Pt}
    (hp : S.walk x p = some y) (hL : S.walk x L = some m) (hs : S.walk m s = some n)
    (hR : S.walk n R = some y) :
    S.toPath p hp = (S.toPath L hL).comp ((S.toPath s hs).comp (S.toPath R hR)) := by
  subst e
  have hLs : S.walk x (L ++ s) = some n := by rw [walk_append, hL, Option.bind_some, hs]
  exact (S.toPath_append hp hLs hR).trans ((congrArg (fun P => Quiver.Path.comp P (S.toPath R hR))
    (S.toPath_append hLs hL hs)).trans
    (Quiver.Path.comp_assoc _ _ _))

theorem nf_unitPath (σ : Bool) (e : Edge S.Pt S.Ed) {x y : S.Pt}
    (h₁ : S.walk x (S.unitPath σ e) = some y) (h₂ : S.walk x [e] = some y) :
    normalizeAux .nil (pathComp S.freePrefunctor (S.toPath _ h₁)) =
      normalizeAux .nil (pathComp S.freePrefunctor (S.toPath _ h₂)) := by
  obtain ⟨rfl, h⟩ := S.walk_cons_eq_some.1 h₂
  obtain rfl : S.tgt e = y := Option.some.inj h
  cases σ <;> cases e <;> rfl

theorem nf_unitor (k : UnitorKind) (e : Edge S.Pt S.Ed) {x y : S.Pt}
    (hs : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some y)
    (ht : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some y) :
    normalizeAux .nil (pathComp S.freePrefunctor (S.toPath _ hs)) =
      normalizeAux .nil (pathComp S.freePrefunctor (S.toPath _ ht)) := by
  cases k
  exacts [S.nf_unitPath false e hs ht, (S.nf_unitPath false e ht hs).symm,
    S.nf_unitPath true e hs ht, (S.nf_unitPath true e ht hs).symm]

def cellEnds (hS : S.WellFormed) (c : S.Ce) : S.Pt × S.Pt :=
  (S.pathEnds (S.cellSource c)).get (hS c).1

theorem walk_cellSource (hS : S.WellFormed) (c : S.Ce) :
    S.walk (S.cellEnds hS c).1 (S.cellSource c) = some (S.cellEnds hS c).2 :=
  S.walk_of_pathEnds (Option.some_get _).symm

theorem walk_cellTarget (hS : S.WellFormed) (c : S.Ce) :
    S.walk (S.cellEnds hS c).1 (S.cellTarget c) = some (S.cellEnds hS c).2 :=
  S.walk_of_pathEnds ((hS c).2.symm.trans (Option.some_get _).symm)

theorem walk_cellType_snd (hS : S.WellFormed) {c : Cell S.Pt S.Ed S.Ce}
    (hc : (S.pathEnds (S.cellType c).1).isSome) :
    S.walk ((S.pathEnds (S.cellType c).1).get hc).1 (S.cellType c).2 =
      some ((S.pathEnds (S.cellType c).1).get hc).2 :=
  S.walk_of_pathEnds ((S.pathEnds_cellType_snd hS c).trans (Option.some_get hc).symm)

variable [DecidableEq S.Ed]

def rewrite (p : List (Edge S.Pt S.Ed)) (l : Cell S.Pt S.Ed S.Ce × ℕ) : List (Edge S.Pt S.Ed) :=
  p.take l.2 ++ (S.cellType l.1).2 ++ p.drop (l.2 + (S.cellType l.1).1.length)

theorem targetFrom_cons_eq_some {p q : List (Edge S.Pt S.Ed)} {l : Cell S.Pt S.Ed S.Ce × ℕ}
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (h : S.targetFrom p (l :: ls) = some q) :
    S.applyLayer p l.1 l.2 = some (S.rewrite p l) ∧ S.targetFrom (S.rewrite p l) ls = some q := by
  obtain ⟨p', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := (S.eq_of_applyLayer_eq_some h₁).2.2
  exact ⟨h₁, h₂⟩

omit [DecidableEq S.Pt] [DecidableEq S.Ed] in
theorem rewrite_gen (c : S.Ce) (L R : List (Edge S.Pt S.Ed)) :
    S.rewrite (L ++ S.cellSource c ++ R) (.gen c, L.length) = L ++ S.cellTarget c ++ R := by
  simp [rewrite, cellType]

theorem targetFrom_of_append_cons_gen {A ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} {c : S.Ce}
    {p q L R : List (Edge S.Pt S.Ed)} (h : S.targetFrom p (A ++ (.gen c, L.length) :: ls) = some q)
    (hA : S.targetFrom p A = some (L ++ S.cellSource c ++ R)) :
    S.targetFrom (L ++ S.cellTarget c ++ R) ls = some q := by
  rw [targetFrom_append, hA, Option.bind_some] at h
  rw [← S.rewrite_gen]
  exact (S.targetFrom_cons_eq_some h).2

theorem isSome_pathEnds_of_applyLayer {p p' : List (Edge S.Pt S.Ed)} {c : Cell S.Pt S.Ed S.Ce}
    {o : ℕ} (hl : S.applyLayer p c o = some p') {x y : S.Pt} (hp : S.walk x p = some y) :
    (S.pathEnds (S.cellType c).1).isSome := by
  obtain ⟨hne, hseg, -⟩ := S.eq_of_applyLayer_eq_some hl
  rw [← hseg, walk_append, walk_append] at hp
  obtain ⟨b, hb, -⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨a, -, hab⟩ := Option.bind_eq_some_iff.1 hb
  exact S.isPath_of_pathEnds (S.pathEnds_eq_some_iff.2 ⟨hne, hab⟩)

theorem walk_of_applyLayer {p p' : List (Edge S.Pt S.Ed)} {c : Cell S.Pt S.Ed S.Ce} {o : ℕ}
    (hl : S.applyLayer p c o = some p') {x y : S.Pt} (hp : S.walk x p = some y) :
    S.walk x (p.take o) = some ((S.pathEnds (S.cellType c).1).get
        (S.isSome_pathEnds_of_applyLayer hl hp)).1 ∧
      S.walk ((S.pathEnds (S.cellType c).1).get (S.isSome_pathEnds_of_applyLayer hl hp)).1
        (S.cellType c).1 = some ((S.pathEnds (S.cellType c).1).get
          (S.isSome_pathEnds_of_applyLayer hl hp)).2 ∧
      S.walk ((S.pathEnds (S.cellType c).1).get (S.isSome_pathEnds_of_applyLayer hl hp)).2
        (p.drop (o + (S.cellType c).1.length)) = some y :=
  S.walk_split (((S.eq_of_applyLayer_eq_some hl).2.1).symm ▸ hp) _

theorem walk_applyLayer (hS : S.WellFormed) {p p' : List (Edge S.Pt S.Ed)}
    {c : Cell S.Pt S.Ed S.Ce} {o : ℕ} (hl : S.applyLayer p c o = some p') {x y : S.Pt}
    (hp : S.walk x p = some y) : S.walk x p' = some y := by
  have h := S.walk_of_applyLayer hl hp
  rw [(S.eq_of_applyLayer_eq_some hl).2.2]
  exact S.walk_append₃ h.1 (S.walk_cellType_snd hS _) h.2.2

theorem walk_targetFrom (hS : S.WellFormed) {p q : List (Edge S.Pt S.Ed)}
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (h : S.targetFrom p ls = some q) {x y : S.Pt}
    (hp : S.walk x p = some y) : S.walk x q = some y := by
  induction ls generalizing p with
  | nil => exact Option.some.inj h ▸ hp
  | cons l ls ih =>
    obtain ⟨h₁, h₂⟩ := S.targetFrom_cons_eq_some h
    exact ih h₂ (S.walk_applyLayer hS h₁ hp)

theorem applyLayer_injective {a a' b : List (Edge S.Pt S.Ed)} {c : Cell S.Pt S.Ed S.Ce} {o : ℕ}
    (h : S.applyLayer a c o = some b) (h' : S.applyLayer a' c o = some b) : a = a' := by
  obtain ⟨-, L, R, rfl, hL, rfl⟩ := S.applyLayer_eq_some_iff.1 h
  obtain ⟨-, L', R', rfl, hL', e⟩ := S.applyLayer_eq_some_iff.1 h'
  rw [List.append_assoc, List.append_assoc] at e
  obtain ⟨rfl, e₂⟩ := List.append_inj e (hL.trans hL'.symm)
  exact congrArg (L ++ (S.cellType c).1 ++ ·) (List.append_cancel_left e₂)

theorem targetFrom_injective {a a' q : List (Edge S.Pt S.Ed)}
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (h : S.targetFrom a ls = some q)
    (h' : S.targetFrom a' ls = some q) : a = a' := by
  induction ls generalizing a a' with
  | nil => exact (Option.some.inj h).trans (Option.some.inj h').symm
  | cons l ls ih =>
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b', hb', h'⟩ := Option.bind_eq_some_iff.1 h'
    obtain rfl := ih h h'
    exact S.applyLayer_injective hb hb'

theorem targetFrom_append₃_eq_some {p q : List (Edge S.Pt S.Ed)}
    {A M Z : List (Cell S.Pt S.Ed S.Ce × ℕ)} (h : S.targetFrom p (A ++ M ++ Z) = some q) :
    ∃ r r', S.targetFrom p A = some r ∧ S.targetFrom r M = some r' ∧
      S.targetFrom r' Z = some q := by
  rw [targetFrom_append, targetFrom_append, Option.bind_assoc] at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨r', hr', h⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨r, r', hr, hr', h⟩

theorem eq_source_of_target_append {d e : Diagram S.Pt S.Ed S.Ce} {r q : List (Edge S.Pt S.Ed)}
    (hr : S.target d = some r) (hq' : S.target e = some q) (hq : S.target (d ++ e) = some q) :
    r = e.source := by
  have h := S.targetFrom_of_target hq
  rw [Diagram.source_append, Diagram.layers_append, targetFrom_append,
    S.targetFrom_of_target hr, Option.bind_some] at h
  exact S.targetFrom_injective h (S.targetFrom_of_target hq')

theorem eq_of_cancel_eq_some {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.cancel d h = some d') :
    ∃ l₁ l₂ rest, d.layers.drop h = l₁ :: l₂ :: rest ∧ (∀ g, l₁.1 ≠ .gen g) ∧
      (∀ g, l₂.1 ≠ .gen g) ∧ d' = ⟨d.source, d.layers.take h ++ rest⟩ ∧
        S.target d' = S.target d := by
  unfold cancel at hd
  split at hd
  · rename_i k₁ e₁ o₁ k₂ e₂ o₂ rest hdrop
    split_ifs at hd with hc
    obtain rfl := (Option.some.inj hd).symm
    have hdrop₂ : d.layers.drop (h + 2) = rest := by
      rw [← List.drop_drop, hdrop]
      rfl
    refine ⟨_, _, rest, hdrop, fun _ => by simp, fun _ => by simp, ?_, ?_⟩
    · rw [hdrop₂]
    simp only [target, if_pos hc.1]
    conv_rhs => rw [← List.take_append_drop (h + 2) d.layers]
    rw [targetFrom_append, targetFrom_append, hc.2.2, hdrop₂]
  · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])

theorem applyLayer_trade {r r₁ r₂ : List (Edge S.Pt S.Ed)} {k : UnitorKind} (hk : k.side = true)
    {e f : Edge S.Pt S.Ed} {o : ℕ}
    (h₁ : S.applyLayer r (.unitor k e : Cell S.Pt S.Ed S.Ce) o = some r₁)
    (h₂ : S.applyLayer r (.unitor k.toLeft f : Cell S.Pt S.Ed S.Ce) (o + 1) = some r₂) {x y : S.Pt}
    (hr : S.walk x r = some y) : r₂ = r₁ := by
  obtain ⟨-, L, R, rfl, rfl, rfl⟩ := S.applyLayer_eq_some_iff.1 h₁
  obtain ⟨-, L', R', e', hL', rfl⟩ := S.applyLayer_eq_some_iff.1 h₂
  cases k <;> simp only [UnitorKind.side, Bool.false_eq_true] at hk <;>
    simp only [cellType, UnitorKind.removes, UnitorKind.side, UnitorKind.toLeft, unitPath,
      cond_true, cond_false, List.append_assoc, List.cons_append, List.nil_append] at e' hr ⊢
  · obtain ⟨rfl, e₂⟩ := List.append_inj (s₁ := L ++ [e]) (by simpa using e')
      (by simp [hL'])
    obtain rfl := (List.cons.inj e₂).2
    simp
  · obtain ⟨rfl, rfl⟩ := List.append_inj (s₁ := L ++ [e]) (by simpa using e')
      (by simp [hL'])
    obtain ⟨a, -, ha⟩ := S.walk_append_eq_some (p := L) (q := e :: f :: R') hr
    have hf := (S.walk_cons_eq_some.1 (S.walk_cons_eq_some.1 ha).2).1
    simp [hf]

omit [DecidableEq S.Pt] [DecidableEq S.Ed] in
theorem layers_eq_of_drop_eq_append {d : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    {M rest : List (Cell S.Pt S.Ed S.Ce × ℕ)} (hdrop : d.layers.drop h = M ++ rest) :
    d.layers = d.layers.take h ++ M ++ rest := by
  rw [List.append_assoc, ← hdrop, List.take_append_drop]

theorem eq_of_trade_eq_some {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.trade d h = some d') :
    ∃ l l' rest, d.layers.drop h = l :: rest ∧ (∀ g, l.1 ≠ .gen g) ∧ (∀ g, l'.1 ≠ .gen g) ∧
      d' = ⟨d.source, d.layers.take h ++ l' :: rest⟩ ∧
        (S.WellFormed → S.target d' = S.target d) := by
  unfold trade at hd
  split at hd
  · rename_i k e o rest hdrop
    split_ifs at hd with hc
    split at hd
    · rename_i before after hb ha
      split at hd
      · rename_i f _
        dsimp only at hd
        split_ifs at hd with ht
        obtain rfl := (Option.some.inj hd).symm
        refine ⟨_, _, rest, hdrop, fun _ => by simp, fun _ => by simp, rfl, fun hS => ?_⟩
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 ht
        have hl := S.layers_eq_of_drop_eq_append (M := [_]) hdrop
        have hq' := S.targetFrom_of_target hq
        dsimp only at hq'
        rw [targetFrom_append, hb, Option.bind_some] at hq'
        obtain ⟨h₂, hr₂⟩ := S.targetFrom_cons_eq_some hq'
        have hget : d.layers[h]? = some (.unitor k e, o) := by
          rw [← Nat.add_zero h, ← List.getElem?_drop, hdrop]
          rfl
        rw [List.take_add_one, hget, Option.toList_some, targetFrom_append, hb,
          Option.bind_some] at ha
        obtain ⟨h₁, -⟩ := S.targetFrom_cons_eq_some ha
        obtain ⟨x, y, hxy⟩ := S.exists_pathEnds_of_isPath hc.1
        have hw := S.walk_targetFrom hS hb (S.walk_of_pathEnds hxy)
        have e₂ := S.applyLayer_trade hc.2 h₁ h₂ hw
        rw [hq, target, if_pos hc.1, hl, List.append_assoc, targetFrom_append, hb, Option.bind_some,
          List.singleton_append]
        exact (congrArg (fun r => S.targetFrom r rest) e₂.symm |>.trans hr₂ |>.symm.trans
          (congrArg (·.bind fun q => S.targetFrom q rest) h₁).symm)
      · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
    · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])

theorem eq_of_slide_eq_some {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.slide d h = some d') :
    ∃ g p k e q f uo go rest, d.layers.drop h = (g, p) :: (.unitor k e, q) :: rest ∧
      S.slideData k e q p (S.cellType g).1 (S.cellType g).2 = some (f, uo, go) ∧
        d' = ⟨d.source, d.layers.take h ++ (.unitor k f, uo) :: (g, go) :: rest⟩ ∧
          S.target d' = S.target d := by
  unfold slide at hd
  split at hd
  · rename_i g p k e q rest hdrop
    split at hd
    · rename_i f uo go hsd
      dsimp only at hd
      split_ifs at hd with ht
      obtain rfl := (Option.some.inj hd).symm
      exact ⟨g, p, k, e, q, f, uo, go, rest, hdrop, hsd, rfl, ht.2⟩
    · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])

theorem take_of_applyLayer {a b : List (Edge S.Pt S.Ed)} {c : Cell S.Pt S.Ed S.Ce} {o i : ℕ}
    (hl : S.applyLayer a c o = some b) (hi : i ≤ o) : b.take i = a.take i := by
  obtain ⟨-, L, R, rfl, rfl, rfl⟩ := S.applyLayer_eq_some_iff.1 hl
  simp only [List.append_assoc, List.take_append, Nat.sub_eq_zero_of_le hi, Nat.zero_sub,
    List.take_zero, List.nil_append]

theorem drop_of_applyLayer {a b : List (Edge S.Pt S.Ed)} {c : Cell S.Pt S.Ed S.Ce} {o : ℕ}
    (hl : S.applyLayer a c o = some b) (j : ℕ) :
    b.drop (o + (S.cellType c).2.length + j) = a.drop (o + (S.cellType c).1.length + j) := by
  obtain ⟨-, L, R, rfl, rfl, rfl⟩ := S.applyLayer_eq_some_iff.1 hl
  rw [← List.length_append, List.drop_length_add_append, ← List.length_append,
    List.drop_length_add_append]

theorem source_unitApply {m : UnitMove} {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.unitApply m d h = some d') : d'.source = d.source := by
  cases m
  · obtain ⟨_, _, _, _, _, _, rfl, _⟩ := S.eq_of_cancel_eq_some hd
    rfl
  · obtain ⟨_, _, _, _, _, _, rfl, _⟩ := S.eq_of_trade_eq_some hd
    rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := S.eq_of_slide_eq_some hd
    rfl

theorem target_unitApply (hS : S.WellFormed) {m : UnitMove} {d d' : Diagram S.Pt S.Ed S.Ce}
    {h : ℕ} (hd : S.unitApply m d h = some d') : S.target d' = S.target d := by
  cases m
  · exact (S.eq_of_cancel_eq_some hd).choose_spec.choose_spec.choose_spec.2.2.2.2
  · exact (S.eq_of_trade_eq_some hd).choose_spec.choose_spec.choose_spec.2.2.2.2 hS
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ht⟩ := S.eq_of_slide_eq_some hd
    exact ht

theorem pathEnds_source_unitApply {m : UnitMove} {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.unitApply m d h = some d') {x y : S.Pt} (hx : S.pathEnds d.source = some (x, y)) :
    S.pathEnds d'.source = some (x, y) :=
  (congrArg S.pathEnds (S.source_unitApply hd)).trans hx

theorem take_or_drop_of_slideData {g : Cell S.Pt S.Ed S.Ce} {k : UnitorKind} {e f : Edge S.Pt S.Ed}
    {p q uo go : ℕ} (hsd : S.slideData k e q p (S.cellType g).1 (S.cellType g).2 = some (f, uo, go))
    {r r₁ r₃ : List (Edge S.Pt S.Ed)} (h₁ : S.applyLayer r g p = some r₁)
    (h₃ : S.applyLayer r (.unitor k f : Cell S.Pt S.Ed S.Ce) uo = some r₃) :
    r₃.take go = r.take p ∨
      r₃.drop (go + (S.cellType g).1.length) = r.drop (p + (S.cellType g).1.length) := by
  have hlen : 0 < (S.cellType g).1.length := List.length_pos_iff.2 (S.eq_of_applyLayer_eq_some h₁).1
  have hdrop := S.drop_of_applyLayer h₃ ((S.cellType g).1.length - 1)
  cases k <;> simp only [slideData] at hsd <;> split_ifs at hsd with hc <;>
    obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.1 hsd <;>
    simp only [Prod.mk.injEq] at ha <;> obtain ⟨-, rfl, rfl⟩ := ha <;>
    simp only [cellType, UnitorKind.removes, UnitorKind.side, unitPath, cond_true, cond_false,
      List.length_cons, List.length_nil] at hdrop
  · refine .inr ?_
    rw [show p - 1 + (S.cellType g).1.length = p - 1 + 1 + ((S.cellType g).1.length - 1) by omega,
      show p + (S.cellType g).1.length = p - 1 + (0 + 1 + 1) + ((S.cellType g).1.length - 1) by
        omega]
    exact hdrop
  · refine .inr ?_
    rw [show p + 1 + (S.cellType g).1.length = p + (0 + 1 + 1) + ((S.cellType g).1.length - 1) by
        omega, show p + (S.cellType g).1.length = p + 1 + ((S.cellType g).1.length - 1) by omega]
    exact hdrop
  · exact .inl (S.take_of_applyLayer h₃ (by omega))
  · exact .inl (S.take_of_applyLayer h₃ (by omega))

theorem eq_of_applyLayer_unit {p p' p₀ : List (Edge S.Pt S.Ed)} {o : ℕ}
    (hl : S.applyLayer p (.unit p₀ : Cell S.Pt S.Ed S.Ce) o = some p') : p' = p :=
  (S.eq_of_applyLayer_eq_some hl).2.2.trans (S.eq_of_applyLayer_eq_some hl).2.1

theorem targetFrom_append_cons_unit {p r : List (Edge S.Pt S.Ed)}
    {A Z : List (Cell S.Pt S.Ed S.Ce × ℕ)} {p₀ : List (Edge S.Pt S.Ed)} {o : ℕ}
    (hA : S.targetFrom p A = some r) (hu : (S.applyLayer r (.unit p₀) o).isSome) :
    S.targetFrom p (A ++ (.unit p₀, o) :: Z) = S.targetFrom p (A ++ Z) := by
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hu
  obtain rfl := S.eq_of_applyLayer_unit hr'
  rw [targetFrom_append, targetFrom_append, hA, Option.bind_some, Option.bind_some, targetFrom,
    hr', Option.bind_some]

omit [DecidableEq S.Ed] in
theorem nf_toPath_append₃ {p L s R : List (Edge S.Pt S.Ed)} (e : L ++ s ++ R = p)
    {x m n y : S.Pt} (hp : S.walk x p = some y) (hL : S.walk x L = some m)
    (hs : S.walk m s = some n) (hR : S.walk n R = some y) :
    normalizeAux .nil (pathComp S.freePrefunctor (S.toPath p hp)) =
      (normalizeAux .nil (pathComp S.freePrefunctor (S.toPath L hL))).comp
        ((normalizeAux .nil (pathComp S.freePrefunctor (S.toPath s hs))).comp
          (normalizeAux .nil (pathComp S.freePrefunctor (S.toPath R hR)))) :=
  (congrArg (fun P => normalizeAux .nil (pathComp S.freePrefunctor P))
    (S.toPath_append₃ e hp hL hs hR)).trans ((nf_pathComp_comp _ _ _).trans
      (congrArg (Quiver.Path.comp _) (nf_pathComp_comp _ _ _)))

end Signature

namespace RelSignature

variable (S : RelSignature.{v'}) [DecidableEq S.Pt] [DecidableEq S.Ed]

omit [DecidableEq S.Pt] [DecidableEq S.Ed] in
theorem source_completeSide (d : Diagram S.Pt S.Ed S.Ce) (r : S.Rel) (α : Bool) (h o : ℕ) :
    (S.completeSide d r α h o).source = d.source := by
  unfold completeSide
  split_ifs <;> rfl

theorem target_of_target_completeSide {d : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {α : Bool}
    {h o : ℕ} {q : List (Edge S.Pt S.Ed)} (hq : S.target (S.completeSide d r α h o) = some q) :
    S.target d = some q := by
  unfold completeSide at hq
  split_ifs at hq with hr
  · have hp := S.isPath_source_of_target hq
    have ht := S.targetFrom_of_target hq
    obtain ⟨r₁, hA, h₁⟩ := Option.bind_eq_some_iff.1
      ((S.targetFrom_append _ _ _).symm.trans ht)
    obtain ⟨_, hu, -⟩ := Option.bind_eq_some_iff.1 h₁
    rw [S.targetFrom_append_cons_unit hA (Option.isSome_iff_exists.2 ⟨_, hu⟩),
      List.take_append_drop] at ht
    exact S.target_mk_of_targetFrom hp ht
  · exact hq

end RelSignature

namespace Signature

variable {B : Type u} [Bicategory.{w, v} B] (S : Signature.{v'}) [DecidableEq S.Pt]

structure BicatInterp (hS : S.WellFormed) (B : Type u) [Bicategory.{w, v} B] where
  toPrefunctor : Prefunctor S.GenQuiver B
  cell (c : S.Ce) :
    pathComp (S.freePrefunctor ⋙q (lift toPrefunctor).toPrefunctor)
        (S.toPath (S.cellSource c) (S.walk_cellSource hS c)) ⟶
      pathComp (S.freePrefunctor ⋙q (lift toPrefunctor).toPrefunctor)
        (S.toPath (S.cellTarget c) (S.walk_cellTarget hS c))

variable {S} {hS : S.WellFormed} (F : S.BicatInterp hS B)

namespace BicatInterp

@[ext]
theorem ext {F F' : S.BicatInterp hS B} (h : F.toPrefunctor = F'.toPrefunctor)
    (hc : ∀ c, F.cell c ≍ F'.cell c) : F = F' := by
  obtain ⟨G, c⟩ := F
  obtain ⟨G', c'⟩ := F'
  obtain rfl : G = G' := h
  congr
  funext x
  exact eq_of_heq (hc x)

abbrev label : Prefunctor S.PathQuiver B := S.freePrefunctor ⋙q (lift F.toPrefunctor).toPrefunctor

def unitorReading (k : UnitorKind) (e : Edge S.Pt S.Ed) {x y : S.Pt}
    (hs : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some y)
    (ht : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some y) :
    pathComp F.label (S.toPath _ hs) ⟶ pathComp F.label (S.toPath _ ht) :=
  eqToHom (pathComp_comp_lift _ _ _) ≫
    (lift F.toPrefunctor).map₂ (homOfNormalizeAuxEq (S.nf_unitor k e hs ht)) ≫
      eqToHom (pathComp_comp_lift _ _ _).symm

def cellReading : (c : Cell S.Pt S.Ed S.Ce) → (hc : (S.pathEnds (S.cellType c).1).isSome) →
    (hs : S.walk ((S.pathEnds (S.cellType c).1).get hc).1 (S.cellType c).1 =
      some ((S.pathEnds (S.cellType c).1).get hc).2) →
    (ht : S.walk ((S.pathEnds (S.cellType c).1).get hc).1 (S.cellType c).2 =
      some ((S.pathEnds (S.cellType c).1).get hc).2) →
    (pathComp F.label (S.toPath _ hs) ⟶ pathComp F.label (S.toPath _ ht))
  | .gen c, _, _, _ => F.cell c
  | .unitor k e, _, hs, ht => F.unitorReading k e hs ht
  | .unit _, _, _, _ => 𝟙 _

def cellFree (c : S.Ce) :
    (lift F.toPrefunctor).map (pathComp S.freePrefunctor
        (S.toPath (S.cellSource c) (S.walk_cellSource hS c))) ⟶
      (lift F.toPrefunctor).map (pathComp S.freePrefunctor
        (S.toPath (S.cellTarget c) (S.walk_cellTarget hS c))) :=
  eqToHom (pathComp_comp_lift _ _ _).symm ≫ F.cell c ≫ eqToHom (pathComp_comp_lift _ _ _)

theorem isStructural_unitorReading (k : UnitorKind) (e : Edge S.Pt S.Ed) {x y : S.Pt}
    (hs : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some y)
    (ht : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some y) :
    IsStructural F.toPrefunctor (pathComp S.freePrefunctor (S.toPath _ hs))
      (pathComp S.freePrefunctor (S.toPath _ ht)) (F.unitorReading k e hs ht) :=
  ⟨_, pathComp_comp_lift _ _ _, (pathComp_comp_lift _ _ _).symm, rfl⟩

theorem unitorReading_eq (k : UnitorKind) (e : Edge S.Pt S.Ed) {x y : S.Pt}
    (hs : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some y)
    (ht : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some y)
    (θ : pathComp S.freePrefunctor (S.toPath _ hs) ⟶ pathComp S.freePrefunctor (S.toPath _ ht)) :
    F.unitorReading k e hs ht = eqToHom (pathComp_comp_lift _ _ _) ≫
      (lift F.toPrefunctor).map₂ θ ≫ eqToHom (pathComp_comp_lift _ _ _).symm :=
  (F.isStructural_unitorReading k e hs ht).eq ⟨θ, _, _, rfl⟩

theorem isStructural_cellReading {c : Cell S.Pt S.Ed S.Ce} (hc : ∀ g, c ≠ .gen g)
    (hp : (S.pathEnds (S.cellType c).1).isSome)
    (hs : S.walk ((S.pathEnds (S.cellType c).1).get hp).1 (S.cellType c).1 =
      some ((S.pathEnds (S.cellType c).1).get hp).2)
    (ht : S.walk ((S.pathEnds (S.cellType c).1).get hp).1 (S.cellType c).2 =
      some ((S.pathEnds (S.cellType c).1).get hp).2) :
    IsStructural F.toPrefunctor (pathComp S.freePrefunctor (S.toPath _ hs))
      (pathComp S.freePrefunctor (S.toPath _ ht)) (F.cellReading c hp hs ht) := by
  cases c with
  | gen g => exact absurd rfl (hc g)
  | unitor k e => exact F.isStructural_unitorReading k e hs ht
  | unit q => exact isStructural_id (pathComp_comp_lift _ _ _)

theorem isSandwich_cellReading (g : S.Ce) (hp : (S.pathEnds (S.cellSource g)).isSome)
    (hs : S.walk ((S.pathEnds (S.cellSource g)).get hp).1 (S.cellSource g) =
      some ((S.pathEnds (S.cellSource g)).get hp).2)
    (ht : S.walk ((S.pathEnds (S.cellSource g)).get hp).1 (S.cellTarget g) =
      some ((S.pathEnds (S.cellSource g)).get hp).2) :
    IsSandwich F.toPrefunctor (pathComp S.freePrefunctor (S.toPath _ hs))
      (pathComp S.freePrefunctor (S.toPath _ ht)) (F.cellFree g)
      (F.cellReading (.gen g) hp hs ht) :=
  (congrArg (IsSandwich _ _ _ _) (eq_eqToHom_conj_conj _ _ _ _ _)).mpr
    (isSandwich_conj (pathComp_comp_lift _ _ _) (F.cellFree g) (pathComp_comp_lift _ _ _).symm)

variable [DecidableEq S.Ed]

def layerReading (c : Cell S.Pt S.Ed S.Ce) (o : ℕ) {p p' : List (Edge S.Pt S.Ed)}
    (hl : S.applyLayer p c o = some p') {x y : S.Pt} (hp : S.walk x p = some y)
    (hp' : S.walk x p' = some y) :
    pathComp F.label (S.toPath p hp) ⟶ pathComp F.label (S.toPath p' hp') :=
  eqToHom (congrArg (pathComp F.label) (S.toPath_append₃
      (S.eq_of_applyLayer_eq_some hl).2.1 hp (S.walk_of_applyLayer hl hp).1
        (S.walk_of_applyLayer hl hp).2.1 (S.walk_of_applyLayer hl hp).2.2)) ≫
    pathWhisker F.label (S.toPath _ (S.walk_of_applyLayer hl hp).1)
      (F.cellReading c _ (S.walk_of_applyLayer hl hp).2.1 (S.walk_cellType_snd hS _))
      (S.toPath _ (S.walk_of_applyLayer hl hp).2.2) ≫
    eqToHom (congrArg (pathComp F.label) (S.toPath_append₃
      (S.eq_of_applyLayer_eq_some hl).2.2.symm hp' (S.walk_of_applyLayer hl hp).1
        (S.walk_cellType_snd hS _) (S.walk_of_applyLayer hl hp).2.2)).symm

def evalFrom : (ls : List (Cell S.Pt S.Ed S.Ce × ℕ)) → (p : List (Edge S.Pt S.Ed)) →
    {x y : S.Pt} → (hp : S.walk x p = some y) → {q : List (Edge S.Pt S.Ed)} →
    S.targetFrom p ls = some q → (hq : S.walk x q = some y) →
    (pathComp F.label (S.toPath p hp) ⟶ pathComp F.label (S.toPath q hq))
  | [], _, _, _, hp, _, h, hq =>
    eqToHom (congrArg (pathComp F.label) (S.toPath_congr (Option.some.inj h) hp hq))
  | l :: ls, p, _, _, hp, _, h, hq =>
    F.layerReading l.1 l.2 (S.targetFrom_cons_eq_some h).1 hp
        (S.walk_applyLayer hS (S.targetFrom_cons_eq_some h).1 hp) ≫
      evalFrom ls (S.rewrite p l) _ (S.targetFrom_cons_eq_some h).2 hq

def evalB (d : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt} (hx : S.pathEnds d.source = some (x, y))
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) :
    pathComp F.label (S.toPath d.source (S.walk_of_pathEnds hx)) ⟶
      pathComp F.label (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS hq hx))) :=
  F.evalFrom d.layers d.source _ (S.targetFrom_of_target hq) _

theorem isStructural_layerReading {c : Cell S.Pt S.Ed S.Ce} (hc : ∀ g, c ≠ .gen g) (o : ℕ)
    {p p' : List (Edge S.Pt S.Ed)} (hl : S.applyLayer p c o = some p') {x y : S.Pt}
    (hp : S.walk x p = some y) (hp' : S.walk x p' = some y) :
    IsStructural F.toPrefunctor (pathComp S.freePrefunctor (S.toPath p hp))
      (pathComp S.freePrefunctor (S.toPath p' hp')) (F.layerReading c o hl hp hp') :=
  (((isStructural_pathWhisker (G := S.freePrefunctor) (S.toPath _ (S.walk_of_applyLayer hl hp).1)
    (S.toPath _ (S.walk_of_applyLayer hl hp).2.2) (F.isStructural_cellReading hc _
      (S.walk_of_applyLayer hl hp).2.1 (S.walk_cellType_snd hS _))).comp_eqToHom _).eqToHom_comp
        _).congr (congrArg _ (S.toPath_append₃ (S.eq_of_applyLayer_eq_some hl).2.1 hp _ _ _).symm)
    (congrArg _ (S.toPath_append₃ (S.eq_of_applyLayer_eq_some hl).2.2.symm hp' _ _ _).symm)

theorem isSandwich_layerReading (g : S.Ce) (o : ℕ) {p p' : List (Edge S.Pt S.Ed)}
    (hl : S.applyLayer p (.gen g) o = some p') {x y : S.Pt} (hp : S.walk x p = some y)
    (hp' : S.walk x p' = some y) :
    IsSandwich F.toPrefunctor (pathComp S.freePrefunctor (S.toPath p hp))
      (pathComp S.freePrefunctor (S.toPath p' hp'))
      (X' := pathComp S.freePrefunctor (S.toPath _ (S.walk_of_applyLayer hl hp).1) ≫
        pathComp S.freePrefunctor (S.toPath (S.cellSource g) (S.walk_cellSource hS g)) ≫
          pathComp S.freePrefunctor (S.toPath _ (S.walk_of_applyLayer hl hp).2.2))
      (Y' := pathComp S.freePrefunctor (S.toPath _ (S.walk_of_applyLayer hl hp).1) ≫
        pathComp S.freePrefunctor (S.toPath (S.cellTarget g) (S.walk_cellTarget hS g)) ≫
          pathComp S.freePrefunctor (S.toPath _ (S.walk_of_applyLayer hl hp).2.2))
      ((lift F.toPrefunctor).map (pathComp S.freePrefunctor
          (S.toPath _ (S.walk_of_applyLayer hl hp).1)) ◁ (F.cellFree g ▷
        (lift F.toPrefunctor).map (pathComp S.freePrefunctor
          (S.toPath _ (S.walk_of_applyLayer hl hp).2.2))))
      (F.layerReading (.gen g) o hl hp hp') :=
  (((isSandwich_pathWhisker (G := S.freePrefunctor) (S.toPath _ (S.walk_of_applyLayer hl hp).1)
    (S.toPath _ (S.walk_of_applyLayer hl hp).2.2) (F.isSandwich_cellReading g _
      (S.walk_of_applyLayer hl hp).2.1 (S.walk_cellType_snd hS (c := .gen g) _))).comp_eqToHom
        _).eqToHom_comp _).congr
    (congrArg _ (S.toPath_append₃ (S.eq_of_applyLayer_eq_some hl).2.1 hp _ _ _).symm)
    (congrArg _ (S.toPath_append₃ (S.eq_of_applyLayer_eq_some hl).2.2.symm hp' _ _ _).symm)

theorem evalFrom_nil {p q : List (Edge S.Pt S.Ed)} {x y : S.Pt} (hp : S.walk x p = some y)
    (h : S.targetFrom p [] = some q) (hq : S.walk x q = some y) :
    F.evalFrom [] p hp h hq =
      eqToHom (congrArg (pathComp F.label) (S.toPath_congr (Option.some.inj h) hp hq)) :=
  rfl

theorem evalFrom_cons (l : Cell S.Pt S.Ed S.Ce × ℕ) (ls : List (Cell S.Pt S.Ed S.Ce × ℕ))
    {p q : List (Edge S.Pt S.Ed)} {x y : S.Pt} (hp : S.walk x p = some y)
    (h : S.targetFrom p (l :: ls) = some q) (hq : S.walk x q = some y) :
    F.evalFrom (l :: ls) p hp h hq =
      F.layerReading l.1 l.2 (S.targetFrom_cons_eq_some h).1 hp
          (S.walk_applyLayer hS (S.targetFrom_cons_eq_some h).1 hp) ≫
        F.evalFrom ls (S.rewrite p l) _ (S.targetFrom_cons_eq_some h).2 hq :=
  rfl

theorem evalFrom_congr {ls ls' : List (Cell S.Pt S.Ed S.Ce × ℕ)} (e : ls = ls')
    {p q : List (Edge S.Pt S.Ed)} {x y : S.Pt} (hp : S.walk x p = some y)
    (h : S.targetFrom p ls = some q) (h' : S.targetFrom p ls' = some q)
    (hq : S.walk x q = some y) : F.evalFrom ls p hp h hq = F.evalFrom ls' p hp h' hq := by
  subst e
  rfl

theorem evalFrom_append : ∀ (ls ls' : List (Cell S.Pt S.Ed S.Ce × ℕ)) (p : List (Edge S.Pt S.Ed))
    {x y : S.Pt} (hp : S.walk x p = some y) {r q : List (Edge S.Pt S.Ed)}
    (h : S.targetFrom p (ls ++ ls') = some q) (h₁ : S.targetFrom p ls = some r)
    (h₂ : S.targetFrom r ls' = some q) (hr : S.walk x r = some y) (hq : S.walk x q = some y),
    F.evalFrom (ls ++ ls') p hp h hq = F.evalFrom ls p hp h₁ hr ≫ F.evalFrom ls' r hr h₂ hq
  | [], ls', p, _, _, hp, _, _, h, h₁, h₂, hr, hq => by
    obtain rfl := Option.some.inj h₁
    exact (Category.id_comp _).symm
  | l :: ls, ls', p, _, _, hp, _, _, h, h₁, h₂, hr, hq =>
    (congrArg (F.layerReading l.1 l.2 _ hp _ ≫ ·) (evalFrom_append ls ls' _ _ _
      (S.targetFrom_cons_eq_some h₁).2 h₂ hr hq)).trans (Category.assoc _ _ _).symm

theorem evalFrom_append₃_congr {A M M' Z : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    {p q : List (Edge S.Pt S.Ed)} {x y : S.Pt} (hp : S.walk x p = some y)
    (h : S.targetFrom p (A ++ M ++ Z) = some q) (h' : S.targetFrom p (A ++ M' ++ Z) = some q)
    (hq : S.walk x q = some y)
    (hloc : ∀ {r r' : List (Edge S.Pt S.Ed)} (hr : S.walk x r = some y)
      (hM : S.targetFrom r M = some r') (hM' : S.targetFrom r M' = some r')
      (hr' : S.walk x r' = some y), F.evalFrom M r hr hM hr' = F.evalFrom M' r hr hM' hr') :
    F.evalFrom (A ++ M ++ Z) p hp h hq = F.evalFrom (A ++ M' ++ Z) p hp h' hq := by
  obtain ⟨r, r', hA, hM, hZ⟩ := S.targetFrom_append₃_eq_some h
  obtain ⟨r₁, r₁', hA', hM', hZ'⟩ := S.targetFrom_append₃_eq_some h'
  obtain rfl : r = r₁ := Option.some.inj (hA.symm.trans hA')
  obtain rfl : r' = r₁' := S.targetFrom_injective hZ hZ'
  have hr := S.walk_targetFrom hS hA hp
  have hr' := S.walk_targetFrom hS hM hr
  have hAM : S.targetFrom p (A ++ M) = some r' := by
    rw [targetFrom_append, hA, Option.bind_some, hM]
  have hAM' : S.targetFrom p (A ++ M') = some r' := by
    rw [targetFrom_append, hA, Option.bind_some, hM']
  rw [F.evalFrom_append _ _ p hp h hAM hZ hr' hq, F.evalFrom_append _ _ p hp hAM hA hM hr hr',
    F.evalFrom_append _ _ p hp h' hAM' hZ hr' hq, F.evalFrom_append _ _ p hp hAM' hA hM' hr hr',
    hloc hr hM hM' hr']

theorem evalB_eq (d : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) :
    F.evalB d hx hq = F.evalFrom d.layers d.source _ (S.targetFrom_of_target hq) _ :=
  rfl

theorem evalB_nil (p : List (Edge S.Pt S.Ed)) {x y : S.Pt} (hx : S.pathEnds p = some (x, y))
    {q : List (Edge S.Pt S.Ed)} (hq : S.target ⟨p, []⟩ = some q) :
    F.evalB ⟨p, []⟩ hx hq = eqToHom (congrArg (pathComp F.label)
      (S.toPath_congr (Option.some.inj (S.targetFrom_of_target hq)) _ _)) :=
  rfl

theorem evalB_singleton (p : List (Edge S.Pt S.Ed)) (l : Cell S.Pt S.Ed S.Ce × ℕ) {x y : S.Pt}
    (hx : S.pathEnds p = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target ⟨p, [l]⟩ = some q) :
    F.evalB ⟨p, [l]⟩ hx hq = F.layerReading l.1 l.2 (S.targetFrom_cons_eq_some
        (S.targetFrom_of_target hq)).1 (S.walk_of_pathEnds hx)
          (S.walk_applyLayer hS (S.targetFrom_cons_eq_some (S.targetFrom_of_target hq)).1
            (S.walk_of_pathEnds hx)) ≫
      eqToHom (congrArg (pathComp F.label)
        (S.toPath_congr (Option.some.inj (S.targetFrom_cons_eq_some
          (S.targetFrom_of_target hq)).2) _ _)) :=
  rfl

theorem evalB_congr {d d' : Diagram S.Pt S.Ed S.Ce} (e : d = d') {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) (hx' : S.pathEnds d'.source = some (x, y))
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hq' : S.target d' = some q) :
    F.evalB d hx hq = eqToHom (congrArg (pathComp F.label)
      (S.toPath_congr (congrArg Diagram.source e) _ _)) ≫ F.evalB d' hx' hq' := by
  subst e
  exact (Category.id_comp _).symm

theorem evalB_append (d e : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {r q : List (Edge S.Pt S.Ed)}
    (hr : S.target d = some r) (hx' : S.pathEnds e.source = some (x, y))
    (hq' : S.target e = some q) (hq : S.target (d ++ e) = some q) :
    F.evalB (d ++ e) hx hq = F.evalB d hx hr ≫ eqToHom (congrArg (pathComp F.label)
      (S.toPath_congr (S.eq_source_of_target_append hr hq' hq) _ _)) ≫
        F.evalB e hx' hq' := by
  obtain ⟨p, ls⟩ := d
  obtain ⟨p', ls'⟩ := e
  obtain rfl : r = p' := S.eq_source_of_target_append hr hq' hq
  rw [eqToHom_refl, Category.id_comp]
  exact F.evalFrom_append ls ls' p _ _ (S.targetFrom_of_target hr) (S.targetFrom_of_target hq') _ _

theorem isStructural_evalFrom : ∀ (ls : List (Cell S.Pt S.Ed S.Ce × ℕ)),
    (∀ l ∈ ls, ∀ g, l.1 ≠ .gen g) → ∀ (p : List (Edge S.Pt S.Ed)) {x y : S.Pt}
    (hp : S.walk x p = some y) {q : List (Edge S.Pt S.Ed)} (h : S.targetFrom p ls = some q)
    (hq : S.walk x q = some y),
    IsStructural F.toPrefunctor (pathComp S.freePrefunctor (S.toPath p hp))
      (pathComp S.freePrefunctor (S.toPath q hq)) (F.evalFrom ls p hp h hq)
  | [], _, p, _, _, hp, _, h, hq => by
    obtain rfl := Option.some.inj h
    exact isStructural_eqToHom (pathComp_comp_lift _ _ _) _
  | l :: ls, hls, p, _, _, hp, _, h, hq =>
    (F.isStructural_layerReading (hls l List.mem_cons_self) l.2 _ hp _).comp
      (isStructural_evalFrom ls (fun l' hl' => hls l' (List.mem_cons_of_mem _ hl')) _ _ _ hq)

theorem evalFrom_eq_of_forall_ne_gen {ls ls' : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    (hls : ∀ l ∈ ls, ∀ g, l.1 ≠ .gen g) (hls' : ∀ l ∈ ls', ∀ g, l.1 ≠ .gen g)
    {p q : List (Edge S.Pt S.Ed)} {x y : S.Pt} (hp : S.walk x p = some y)
    (h : S.targetFrom p ls = some q) (h' : S.targetFrom p ls' = some q)
    (hq : S.walk x q = some y) : F.evalFrom ls p hp h hq = F.evalFrom ls' p hp h' hq :=
  (F.isStructural_evalFrom ls hls p hp h hq).eq (F.isStructural_evalFrom ls' hls' p hp h' hq)

theorem evalB_eq_of_layers {d d' : Diagram S.Pt S.Ed S.Ce}
    {A M M' Z : List (Cell S.Pt S.Ed S.Ce × ℕ)} (hsrc : d'.source = d.source)
    (hl : d.layers = A ++ M ++ Z) (hl' : d'.layers = A ++ M' ++ Z) {x y : S.Pt}
    (hloc : ∀ {r r' : List (Edge S.Pt S.Ed)} (hr : S.walk x r = some y)
      (hM : S.targetFrom r M = some r') (hM' : S.targetFrom r M' = some r')
      (hr' : S.walk x r' = some y), F.evalFrom M r hr hM hr' = F.evalFrom M' r hr hM' hr')
    (hx : S.pathEnds d.source = some (x, y)) (hx' : S.pathEnds d'.source = some (x, y))
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hq' : S.target d' = some q) :
    F.evalB d hx hq = eqToHom (congrArg (pathComp F.label)
      (S.toPath_congr hsrc.symm _ _)) ≫ F.evalB d' hx' hq' := by
  obtain ⟨p, ls⟩ := d
  obtain ⟨p', ls'⟩ := d'
  obtain rfl : p' = p := hsrc
  dsimp only at hl hl'
  subst hl hl'
  rw [eqToHom_refl, Category.id_comp]
  exact F.evalFrom_append₃_congr _ _ _ _ hloc

private theorem comp_comp_cancel {V : Type*} [Quiver V] {a b c d : V}
    {L L' : Quiver.Path a b} {s : Quiver.Path b c} {R R' : Quiver.Path c d}
    (h : L.comp (s.comp R) = L'.comp (s.comp R')) (hLR : L = L' ∨ R = R') : L = L' ∧ R = R' := by
  rcases hLR with rfl | rfl
  · exact ⟨rfl, Quiver.Path.comp_inj_right.1 (Quiver.Path.comp_inj_right.1 h)⟩
  · rw [← Quiver.Path.comp_assoc, ← Quiver.Path.comp_assoc] at h
    exact ⟨Quiver.Path.comp_inj_left.1 (Quiver.Path.comp_inj_left.1 h), rfl⟩

theorem evalFrom_slide {g : Cell S.Pt S.Ed S.Ce} {k : UnitorKind} {e f : Edge S.Pt S.Ed}
    {p q uo go : ℕ} (hsd : S.slideData k e q p (S.cellType g).1 (S.cellType g).2 = some (f, uo, go))
    {r r' : List (Edge S.Pt S.Ed)} {x y : S.Pt} (hr : S.walk x r = some y)
    (hM : S.targetFrom r [(g, p), (.unitor k e, q)] = some r')
    (hM' : S.targetFrom r [(.unitor k f, uo), (g, go)] = some r') (hr' : S.walk x r' = some y) :
    F.evalFrom [(g, p), (.unitor k e, q)] r hr hM hr' =
      F.evalFrom [(.unitor k f, uo), (g, go)] r hr hM' hr' := by
  cases g with
  | unitor _ _ => exact F.evalFrom_eq_of_forall_ne_gen (by simp) (by simp) hr hM hM' hr'
  | unit _ => exact F.evalFrom_eq_of_forall_ne_gen (by simp) (by simp) hr hM hM' hr'
  | gen c =>
    obtain ⟨h₁, h₁'⟩ := S.targetFrom_cons_eq_some hM
    obtain ⟨h₃, h₃'⟩ := S.targetFrom_cons_eq_some hM'
    obtain ⟨h₄, h₄'⟩ := S.targetFrom_cons_eq_some h₃'
    have hw₁ := S.walk_applyLayer hS h₁ hr
    have hw₃ := S.walk_applyLayer hS h₃ hr
    have hw₄ := S.walk_applyLayer hS h₄ hw₃
    have hold := (F.isSandwich_layerReading c p h₁ hr hw₁).comp_isStructural
      (F.isStructural_evalFrom _ (by simp) _ hw₁ h₁' hr')
    have hu := F.isStructural_layerReading (c := .unitor k f) (by simp) uo h₃ hr hw₃
    have hnew := hu.comp_isSandwich ((F.isSandwich_layerReading c go h₄ hw₃ hw₄).comp_isStructural
      (F.isStructural_evalFrom [] (by simp) _ hw₄ h₄' hr'))
    have hnf := (S.nf_toPath_append₃ (S.eq_of_applyLayer_eq_some h₁).2.1 hr
      (S.walk_of_applyLayer h₁ hr).1 (S.walk_of_applyLayer h₁ hr).2.1
        (S.walk_of_applyLayer h₁ hr).2.2).symm.trans ((nf_eq_of_isStructural hu).trans
      (S.nf_toPath_append₃ (S.eq_of_applyLayer_eq_some h₄).2.1 hw₃
        (S.walk_of_applyLayer h₄ hw₃).1 (S.walk_of_applyLayer h₄ hw₃).2.1
          (S.walk_of_applyLayer h₄ hw₃).2.2))
    have hLR := comp_comp_cancel hnf (by
      rcases S.take_or_drop_of_slideData hsd h₁ h₃ with h | h
      · exact .inl (congrArg (fun P => normalizeAux .nil (pathComp S.freePrefunctor P))
          (S.toPath_congr h.symm _ _))
      · exact .inr (congrArg (fun P => normalizeAux .nil (pathComp S.freePrefunctor P))
          (S.toPath_congr h.symm _ _)))
    exact hold.eq (hnew.trans (isSandwich_whisker_congr (F.cellFree c) hLR.1.symm hLR.2.symm))

theorem evalB_eq_of_unitApply (m : UnitMove) {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.unitApply m d h = some d') {x y : S.Pt} (hx : S.pathEnds d.source = some (x, y))
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) :
    F.evalB d hx hq = eqToHom (congrArg (pathComp F.label)
      (S.toPath_congr (S.source_unitApply hd).symm _ _)) ≫
        F.evalB d' (S.pathEnds_source_unitApply hd hx) ((S.target_unitApply hS hd).trans hq) := by
  cases m
  · obtain ⟨l₁, l₂, rest, hdrop, h₁, h₂, rfl, -⟩ := S.eq_of_cancel_eq_some hd
    refine F.evalB_eq_of_layers (d := d) (d' := ⟨d.source, d.layers.take h ++ rest⟩)
      (A := d.layers.take h) (M := [l₁, l₂]) (M' := []) (Z := rest) rfl
      (S.layers_eq_of_drop_eq_append (M := [_, _]) hdrop) (by simp)
      (fun hr hM hM' hr' => F.evalFrom_eq_of_forall_ne_gen ?_ (by simp) hr hM hM' hr') _ _ _ _
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro l (rfl | rfl)
      exacts [h₁, h₂]
  · obtain ⟨l, l', rest, hdrop, h₁, h₂, rfl, -⟩ := S.eq_of_trade_eq_some hd
    refine F.evalB_eq_of_layers (d := d) (d' := ⟨d.source, d.layers.take h ++ l' :: rest⟩)
      (A := d.layers.take h) (M := [l]) (M' := [l']) (Z := rest) rfl
      (S.layers_eq_of_drop_eq_append (M := [_]) hdrop) (by simp)
      (fun hr hM hM' hr' => F.evalFrom_eq_of_forall_ne_gen (by simpa using h₁) (by simpa using h₂)
        hr hM hM' hr') _ _ _ _
  · obtain ⟨g, p, k, e, q', f, uo, go, rest, hdrop, hsd, rfl, -⟩ := S.eq_of_slide_eq_some hd
    refine F.evalB_eq_of_layers (d := d)
      (d' := ⟨d.source, d.layers.take h ++ (.unitor k f, uo) :: (g, go) :: rest⟩)
      (A := d.layers.take h) (M := [(g, p), (.unitor k e, q')])
      (M' := [(.unitor k f, uo), (g, go)]) (Z := rest) rfl
      (S.layers_eq_of_drop_eq_append (M := [_, _]) hdrop) (by simp)
      (fun hr hM hM' hr' => F.evalFrom_slide hsd hr hM hM' hr') _ _ _ _

theorem layerReading_unit (p₀ : List (Edge S.Pt S.Ed)) (o : ℕ) {p p' : List (Edge S.Pt S.Ed)}
    (hl : S.applyLayer p (.unit p₀) o = some p') {x y : S.Pt} (hp : S.walk x p = some y)
    (hp' : S.walk x p' = some y) :
    F.layerReading (.unit p₀) o hl hp hp' = eqToHom (congrArg (pathComp F.label)
      (S.toPath_congr (S.eq_of_applyLayer_unit hl).symm hp hp')) := by
  refine ((congrArg (fun φ => eqToHom _ ≫ φ ≫ eqToHom _) (pathWhisker_id _ _ _ _)).trans ?_)
  exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (eqToHom_trans _ _)

theorem eqToHom_comp_evalFrom (ls : List (Cell S.Pt S.Ed S.Ce × ℕ)) {p p' q : List (Edge S.Pt S.Ed)}
    (e : p = p') {x y : S.Pt} (hp : S.walk x p = some y) (hp' : S.walk x p' = some y)
    (h : S.targetFrom p ls = some q) (h' : S.targetFrom p' ls = some q)
    (hq : S.walk x q = some y) :
    eqToHom (congrArg (pathComp F.label) (S.toPath_congr e hp hp')) ≫
      F.evalFrom ls p' hp' h' hq = F.evalFrom ls p hp h hq := by
  subst e
  exact Category.id_comp _

theorem evalFrom_append_cons_unit (A Z : List (Cell S.Pt S.Ed S.Ce × ℕ))
    (p₀ : List (Edge S.Pt S.Ed)) (o : ℕ) {p q : List (Edge S.Pt S.Ed)} {x y : S.Pt}
    (hp : S.walk x p = some y) (h : S.targetFrom p (A ++ (.unit p₀, o) :: Z) = some q)
    (h' : S.targetFrom p (A ++ Z) = some q) (hq : S.walk x q = some y) :
    F.evalFrom (A ++ (.unit p₀, o) :: Z) p hp h hq = F.evalFrom (A ++ Z) p hp h' hq := by
  obtain ⟨r, hA, hr⟩ := Option.bind_eq_some_iff.1 ((S.targetFrom_append _ _ _).symm.trans h)
  obtain ⟨hu, hZ⟩ := S.targetFrom_cons_eq_some hr
  have hZ' : S.targetFrom r Z = some q := by
    rw [← S.eq_of_applyLayer_unit hu]
    exact hZ
  have hw := S.walk_targetFrom hS hA hp
  rw [F.evalFrom_append _ _ p hp h hA hr hw hq, F.evalFrom_append _ _ p hp h' hA hZ' hw hq,
    evalFrom_cons, layerReading_unit,
    F.eqToHom_comp_evalFrom Z (S.eq_of_applyLayer_unit hu).symm hw _ hZ' hZ hq]

theorem evalFrom_of_forall_ne_gen (ls : List (Cell S.Pt S.Ed S.Ce × ℕ))
    (hls : ∀ l ∈ ls, ∀ g, l.1 ≠ .gen g) {p q : List (Edge S.Pt S.Ed)} {x y : S.Pt}
    {hp : S.walk x p = some y} {h : S.targetFrom p ls = some q} {hq : S.walk x q = some y}
    {φ : pathComp F.label (S.toPath p hp) ⟶ pathComp F.label (S.toPath q hq)}
    (hφ : IsStructural F.toPrefunctor (pathComp S.freePrefunctor (S.toPath p hp))
      (pathComp S.freePrefunctor (S.toPath q hq)) φ) :
    F.evalFrom ls p hp h hq = φ :=
  (F.isStructural_evalFrom ls hls p hp h hq).eq hφ

theorem evalFrom_gen (A : List (Cell S.Pt S.Ed S.Ce × ℕ)) (hA : ∀ l ∈ A, ∀ g, l.1 ≠ .gen g)
    {c : S.Ce} (L R : List (Edge S.Pt S.Ed)) {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    {p q : List (Edge S.Pt S.Ed)} {x y : S.Pt} {hp : S.walk x p = some y}
    {h : S.targetFrom p (A ++ (.gen c, L.length) :: ls) = some q} {hq : S.walk x q = some y}
    (hL : S.walk x L = some (S.cellEnds hS c).1) (hR : S.walk (S.cellEnds hS c).2 R = some y)
    (hpA : S.targetFrom p A = some (L ++ S.cellSource c ++ R))
    {φ : pathComp F.label (S.toPath p hp) ⟶
      (lift F.toPrefunctor).map (pathComp S.freePrefunctor (S.toPath L hL)) ≫
        (lift F.toPrefunctor).map
          (pathComp S.freePrefunctor (S.toPath (S.cellSource c) (S.walk_cellSource hS c))) ≫
          (lift F.toPrefunctor).map (pathComp S.freePrefunctor (S.toPath R hR))}
    (hφ : IsStructural F.toPrefunctor (pathComp S.freePrefunctor (S.toPath p hp))
      (pathComp S.freePrefunctor (S.toPath L hL) ≫
        pathComp S.freePrefunctor (S.toPath (S.cellSource c) (S.walk_cellSource hS c)) ≫
          pathComp S.freePrefunctor (S.toPath R hR)) φ)
    {φ' : (lift F.toPrefunctor).map (pathComp S.freePrefunctor (S.toPath L hL)) ≫
        (lift F.toPrefunctor).map
          (pathComp S.freePrefunctor (S.toPath (S.cellTarget c) (S.walk_cellTarget hS c))) ≫
          (lift F.toPrefunctor).map (pathComp S.freePrefunctor (S.toPath R hR)) ⟶
        pathComp F.label (S.toPath (L ++ S.cellTarget c ++ R)
          (S.walk_append₃ hL (S.walk_cellTarget hS c) hR))}
    (hφ' : IsStructural F.toPrefunctor (pathComp S.freePrefunctor (S.toPath L hL) ≫
        pathComp S.freePrefunctor (S.toPath (S.cellTarget c) (S.walk_cellTarget hS c)) ≫
          pathComp S.freePrefunctor (S.toPath R hR))
      (pathComp S.freePrefunctor (S.toPath (L ++ S.cellTarget c ++ R)
        (S.walk_append₃ hL (S.walk_cellTarget hS c) hR))) φ')
    {rest : pathComp F.label (S.toPath (L ++ S.cellTarget c ++ R)
        (S.walk_append₃ hL (S.walk_cellTarget hS c) hR)) ⟶ pathComp F.label (S.toPath q hq)}
    (hrest : F.evalFrom ls (L ++ S.cellTarget c ++ R)
      (S.walk_append₃ hL (S.walk_cellTarget hS c) hR) (S.targetFrom_of_append_cons_gen h hpA) hq =
        rest) :
    F.evalFrom (A ++ (.gen c, L.length) :: ls) p hp h hq = φ ≫ ((lift F.toPrefunctor).map
      (pathComp S.freePrefunctor (S.toPath L hL)) ◁ (F.cellFree c ▷ (lift F.toPrefunctor).map
        (pathComp S.freePrefunctor (S.toPath R hR)))) ≫ φ' ≫ rest := by
  subst hrest
  have hw := S.walk_targetFrom hS hpA hp
  have h₂ : S.targetFrom (L ++ S.cellSource c ++ R) ((.gen c, L.length) :: ls) = some q := by
    rw [targetFrom_append, hpA, Option.bind_some] at h
    exact h
  have hrw := S.rewrite_gen c L R
  have hp' := S.walk_append₃ hL (S.walk_cellTarget hS c) hR
  obtain ⟨h₃, h₄⟩ := S.targetFrom_cons_eq_some h₂
  rw [F.evalFrom_append A _ p hp h hpA h₂ hw hq, F.evalFrom_cons,
    ← F.eqToHom_comp_evalFrom ls hrw _ hp' h₄ (S.targetFrom_of_append_cons_gen h hpA) hq]
  have key := IsSandwich.eq ((F.isStructural_evalFrom A hA p hp hpA hw).comp_isSandwich
    (((F.isSandwich_layerReading c L.length h₃ hw (S.walk_applyLayer hS h₃ hw)).comp_eqToHom
      (congrArg (pathComp F.label) (S.toPath_congr hrw _ hp'))).congr_whisker
      (congrArg _ (S.toPath_congr (by simp) _ hL))
      (congrArg _ (S.toPath_congr (by simp [cellType]) _ hR)) |>.congr rfl
        (congrArg _ (S.toPath_congr hrw _ hp'))))
    (hφ.comp_isSandwich ((isSandwich_self rfl rfl).comp_isStructural hφ'))
  refine Eq.trans ?_ ((eq_whisker key _).trans
    ((Category.assoc _ _ _).trans (congrArg (φ ≫ ·) (Category.assoc _ _ _))))
  exact (congrArg (F.evalFrom A p hp hpA hw ≫ ·) (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm

theorem evalB_heq_of_eq {d d' : Diagram S.Pt S.Ed S.Ce} (e : d = d') {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) (hx' : S.pathEnds d'.source = some (x, y))
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hq' : S.target d' = some q) :
    F.evalB d hx hq ≍ F.evalB d' hx' hq' := by
  subst e
  rfl

end BicatInterp

end Signature

namespace RelSignature

variable {B : Type u} [Bicategory.{w, v} B] {S : RelSignature.{v'}} [DecidableEq S.Pt]
  [DecidableEq S.Ed] {hS : S.toSignature.WellFormed}

theorem evalB_completeSide (F : S.toSignature.BicatInterp hS B) {d : Diagram S.Pt S.Ed S.Ce}
    {r : S.Rel} {α : Bool} {h o : ℕ} {x y : S.Pt}
    (hx : S.pathEnds (S.completeSide d r α h o).source = some (x, y))
    {q : List (Edge S.Pt S.Ed)} (hq : S.target (S.completeSide d r α h o) = some q) :
    F.evalB (S.completeSide d r α h o) hx hq = eqToHom (congrArg (pathComp F.label)
      (S.toPath_congr (S.source_completeSide d r α h o) _ _)) ≫
        F.evalB d ((congrArg S.pathEnds (S.source_completeSide d r α h o)).symm.trans hx)
          (S.target_of_target_completeSide hq) := by
  have hq' := S.target_of_target_completeSide hq
  have hx' := (congrArg S.pathEnds (S.source_completeSide d r α h o)).symm.trans hx
  by_cases hr : (S.side r α).layers = []
  · have e : S.completeSide d r α h o =
        ⟨d.source, d.layers.take h ++ (.unit (S.side r α).source, o) :: d.layers.drop h⟩ :=
      if_pos hr
    rw [F.evalB_congr e hx hx' hq ((congrArg S.target e).symm.trans hq)]
    congr 1
    refine (F.evalFrom_append_cons_unit _ _ _ _ _ _ ?_ _).trans
      (F.evalFrom_congr (List.take_append_drop h d.layers) _ _ _ _)
    rw [List.take_append_drop]
    exact S.targetFrom_of_target hq'
  · have e : S.completeSide d r α h o = d := if_neg hr
    exact F.evalB_congr e hx hx' hq hq'

end RelSignature

end Atoms.Diagrammatic.Layered
