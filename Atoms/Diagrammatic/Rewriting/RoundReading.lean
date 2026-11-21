import Atoms.Diagrammatic.Rewriting.Equivalence
import Atoms.Diagrammatic.Rewriting.Reading
import Atoms.Diagrammatic.Context.RoundBicategoryCoherence

open CategoryTheory Bicategory Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic

namespace RoundBicat

variable {X : DiagSet.{u}} {n : ℕ} {a b : RoundBicat X n}

theorem Hom.eq_of_mem {f g : a ⟶ b} {x : PastingDiagram X} (hf : f.Mem x) (hg : g.Mem x) :
    f = g := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  obtain ⟨q, rfl⟩ := Arrow.hom_surjective g
  exact (Arrow.hom_eq_hom_iff p q).2
    (((Arrow.mem_hom p x).1 hf).trans ((Arrow.mem_hom q x).1 hg).symm)

namespace Cell

variable {f g h : a ⟶ b}

noncomputable def ofRounding (y : PastingDiagram X) (hy : y.dim = n + 1 + 1)
    (hs : f.Mem (y.boundary (n + 1) false)) (ht : g.Mem (y.boundary (n + 1) true)) : Cell f g where
  diag := ⟨y.rounding (n + 1), isRound_rounding hy ht.isRound⟩
  dim_diag := (HasBdry.rounding ⟨hy, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩).dim_h
  source := hs.of_equiv (HasBdry.rounding ⟨hy, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩).side.symm
  target := ht.of_equiv (HasBdry.rounding ⟨hy, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩).other.symm

end Cell

theorem homMk_ofRounding_congr {f g : a ⟶ b} {y y' : PastingDiagram X} (e : y.Equiv y')
    (hy : y.dim = n + 1 + 1) (hs : f.Mem (y.boundary (n + 1) false))
    (ht : g.Mem (y.boundary (n + 1) true)) (hy' : y'.dim = n + 1 + 1)
    (hs' : f.Mem (y'.boundary (n + 1) false)) (ht' : g.Mem (y'.boundary (n + 1) true)) :
    homMk (Cell.ofRounding y hy hs ht) = homMk (Cell.ofRounding y' hy' hs' ht') :=
  (homMk_eq_homMk_iff _ _).2 (equivalent_of_equiv (e.rounding (by omega)))

theorem equivalent_of_homMk_heq {f g f' g' : a ⟶ b} (t : Cell f g) (t' : Cell f' g') (hf : f = f')
    (hg : g = g') (h : homMk t ≍ homMk t') : Equivalent t.diag t'.diag := by
  subst hf hg
  exact (homMk_eq_homMk_iff _ _).1 (eq_of_heq h)

theorem homMk_ofRounding_diag {f g : a ⟶ b} (t : Cell f g) :
    homMk (Cell.ofRounding t.diag.toPastingDiagram t.dim_diag t.source t.target) = homMk t := by
  have hk : n + 1 < t.diag.dim := by rw [t.dim_diag]; omega
  have hp := pastable_unit_boundary hk
  rw [homMk_eq_homMk_iff]
  refine equivalent_symm (equivalent_trans (equivalent_paste_unit_cond true t.diag t.dim_diag hp
    ((PastingDiagram.equiv_of_eq (rounding_eq hk)).isRound_iff.1
      (Cell.ofRounding t.diag.toPastingDiagram t.dim_diag t.source t.target).diag.isRound))
    (equivalent_of_equiv (PastingDiagram.equiv_of_eq (rounding_eq hk).symm)))

theorem homMk_ofRounding_unit {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x)
    (hy : x.unit.dim = n + 1 + 1) (hs : f.Mem (x.unit.boundary (n + 1) false))
    (ht : f.Mem (x.unit.boundary (n + 1) true)) :
    homMk (Cell.ofRounding x.unit hy hs ht) = 𝟙 f :=
  (homMk_ofRounding_diag (Cell.unitOf hx hx)).trans (homMk_unit_of_mem hx)

theorem homMk_ofRounding_comp {f g h : a ⟶ b} {y z : PastingDiagram X}
    (hy : y.dim = n + 1 + 1) (hs : f.Mem (y.boundary (n + 1) false))
    (ht : g.Mem (y.boundary (n + 1) true)) (hz : z.dim = n + 1 + 1)
    (hs' : g.Mem (z.boundary (n + 1) false)) (ht' : h.Mem (z.boundary (n + 1) true))
    (hp : y.Pastable z (n + 1)) (hyz : (y.paste z (n + 1) hp).dim = n + 1 + 1)
    (hs'' : f.Mem ((y.paste z (n + 1) hp).boundary (n + 1) false))
    (ht'' : h.Mem ((y.paste z (n + 1) hp).boundary (n + 1) true)) :
    homMk (Cell.ofRounding y hy hs ht) ≫ homMk (Cell.ofRounding z hz hs' ht') =
      homMk (Cell.ofRounding _ hyz hs'' ht'') := by
  obtain ⟨_, _, _, _, E⟩ := equivalent_rounding_paste (k := n)
    ⟨hy, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩
    ⟨hz, ht.dim_eq, ht'.dim_eq, (hs'.equiv ht), .refl _⟩ ht.isRound ht'.isRound
  rw [homMk_comp_homMk, homMk_eq_homMk_iff]
  exact E

theorem homMk_comp_homMk_reverse {f g : a ⟶ b} (t : Cell f g) (hu : t.diag.IsDegenerate)
    (t' : Cell g f) (ht' : t'.diag.toPastingDiagram = t.diag.reverse hu) :
    homMk t ≫ homMk t' = 𝟙 f := by
  let D := (BiInvData.ofIsDegenerate t.diag hu).mono
    (fun d hd => mem_equivalences_of_isDegenerate d hd)
  have hk : t.diag.dim - 1 = n + 1 := by rw [t.dim_diag]; rfl
  have e₁ : (t.comp t').diag.toPastingDiagram.Equiv
      ((cond false (D.inverse false).toPastingDiagram t.diag.toPastingDiagram).paste
        (cond false t.diag.toPastingDiagram (D.inverse false).toPastingDiagram) (t.diag.dim - 1)
        (D.pastable false)) := by
    have key : ∀ {y y' : PastingDiagram X} {k k' : ℕ} (_ : k = k') (_ : y = y')
        (hp : t.diag.Pastable y k) (hp' : t.diag.Pastable y' k'),
        (t.diag.paste y k hp).Equiv (t.diag.paste y' k' hp') := by
      rintro y y' k k' rfl rfl hp hp'
      exact .refl _
    exact key hk.symm ht' (t.pastable t') (D.pastable false)
  have hr := e₁.isRound_iff.1 (t.comp t').diag.isRound
  rw [homMk_comp_homMk, id_eq_homMk, homMk_eq_homMk_iff]
  refine equivalent_trans (equivalent_of_equiv e₁) (equivalent_trans
    (D.equivalent_invertor false hr) (equivalent_of_equiv ?_))
  exact Equiv.unit (((PastingDiagram.equiv_of_eq
    (boundary_congr t.diag.toPastingDiagram hk false)).trans (t.source.equiv f.mem_rep)))

theorem homMk_ofRounding_heq {f f' g g' : a ⟶ b} (hf : f = f') (hg : g = g')
    {y y' : PastingDiagram X} (e : y.Equiv y') (hy : y.dim = n + 1 + 1)
    (hs : f.Mem (y.boundary (n + 1) false)) (ht : g.Mem (y.boundary (n + 1) true))
    (hy' : y'.dim = n + 1 + 1) (hs' : f'.Mem (y'.boundary (n + 1) false))
    (ht' : g'.Mem (y'.boundary (n + 1) true)) :
    homMk (Cell.ofRounding y hy hs ht) ≍ homMk (Cell.ofRounding y' hy' hs' ht') := by
  subst hf hg
  exact heq_of_eq (homMk_ofRounding_congr e _ _ _ _ _ _)

theorem whiskerLeft_homMk_ofRounding {c : RoundBicat X n} {f : a ⟶ b} {g h : b ⟶ c}
    {x w : PastingDiagram X} (hx : f.Mem x) (hw : w.dim = n + 1 + 1)
    (hs : g.Mem (w.boundary (n + 1) false)) (ht : h.Mem (w.boundary (n + 1) true))
    (hp : x.Pastable w n) (hxw : (x.paste w n hp).dim = n + 1 + 1)
    (hs' : (f ≫ g).Mem ((x.paste w n hp).boundary (n + 1) false))
    (ht' : (f ≫ h).Mem ((x.paste w n hp).boundary (n + 1) true)) :
    f ◁ homMk (Cell.ofRounding w hw hs ht) = homMk (Cell.ofRounding _ hxw hs' ht') := by
  exact (whiskerLeft_homMk_of_mem hx _).trans
    ((homMk_whiskerLeftOf_rounding hx hw hs ht _ _ _).trans
      ((homMk_eq_homMk_iff _ _).2 (equivalent_refl _)))

theorem homMk_ofRounding_whiskerRight {c : RoundBicat X n} {f g : a ⟶ b} {h : b ⟶ c}
    {z w : PastingDiagram X} (hz : h.Mem z) (hw : w.dim = n + 1 + 1)
    (hs : f.Mem (w.boundary (n + 1) false)) (ht : g.Mem (w.boundary (n + 1) true))
    (hp : w.Pastable z n) (hwz : (w.paste z n hp).dim = n + 1 + 1)
    (hs' : (f ≫ h).Mem ((w.paste z n hp).boundary (n + 1) false))
    (ht' : (g ≫ h).Mem ((w.paste z n hp).boundary (n + 1) true)) :
    homMk (Cell.ofRounding w hw hs ht) ▷ h = homMk (Cell.ofRounding _ hwz hs' ht') := by
  exact (homMk_whiskerRight_of_mem hz _).trans
    ((homMk_whiskerRightOf_rounding hz hw hs ht _ _ _).trans
      ((homMk_eq_homMk_iff _ _).2 (equivalent_refl _)))

section Whisker

variable {c : RoundBicat X n}

theorem rightUnitor_inv_heq {f f' : a ⟶ b} (h : f = f') : (ρ_ f).inv ≍ (ρ_ f').inv := by
  subst h; rfl

theorem rightUnitor_hom_heq {f f' : a ⟶ b} (h : f = f') : (ρ_ f).hom ≍ (ρ_ f').hom := by
  subst h; rfl

theorem _root_.CategoryTheory.Iso.inv_heq_inv {C : Type*} [Category C] {A B A' B' : C}
    {e : A ≅ B} {e' : A' ≅ B'} (hA : A = A') (hB : B = B') (h : e.hom ≍ e'.hom) :
    e.inv ≍ e'.inv := by
  subst hA hB
  obtain rfl := Iso.ext (eq_of_heq h)
  rfl

theorem heq_comp_whiskerRight_comp {S T : a ⟶ b} {H : b ⟶ c} (θ : S ⟶ T) {U V W Z : a ⟶ c}
    (φ : U ⟶ V) (η : V ⟶ W) (ψ : W ⟶ Z) (hU : U = (𝟙 a ≫ S) ≫ H)
    (hV : V = ((𝟙 a ≫ S) ≫ 𝟙 b) ≫ H) (hW : W = (𝟙 a ≫ T) ≫ 𝟙 b ≫ H)
    (hZ : Z = (𝟙 a ≫ T) ≫ H) (hφ : φ ≍ (ρ_ (𝟙 a ≫ S)).inv ▷ H)
    (hη : η ≍ (𝟙 a ◁ θ) ▷ (𝟙 b ≫ H)) (hψ : ψ ≍ (ρ_ (𝟙 a ≫ T)).hom ▷ H) :
    φ ≫ η ≫ ψ ≍ 𝟙 a ◁ (θ ▷ H) := by
  subst hU hV hW hZ
  obtain rfl := eq_of_heq hφ
  have hψ' : ψ = eqToHom (assoc _ _ _).symm ≫ (ρ_ (𝟙 a ≫ T)).hom ▷ H := by
    rw [(conj_eqToHom_iff_heq' _ _ (assoc _ _ _).symm rfl).2 hψ, eqToHom_refl, Category.comp_id]
  have hη' : η = eqToHom (assoc _ _ _) ≫ (𝟙 a ◁ θ) ▷ (𝟙 b ≫ H) := by
    rw [(conj_eqToHom_iff_heq' _ _ (assoc _ _ _) rfl).2 hη, eqToHom_refl, Category.comp_id]
  subst hψ' hη'
  have key : (ρ_ (𝟙 a ≫ S)).inv ▷ H ≫ (α_ _ _ _).hom ≫ (𝟙 a ◁ θ) ▷ (𝟙 b ≫ H) ≫
      (α_ _ _ _).inv ≫ (ρ_ (𝟙 a ≫ T)).hom ▷ H =
        (α_ _ _ _).hom ≫ 𝟙 a ◁ (θ ▷ H) ≫ (α_ _ _ _).inv := by
    bicategory
  refine (conj_eqToHom_iff_heq' _ _ (assoc _ _ _) (assoc _ _ _).symm).1 ?_
  simp only [Category.assoc]
  exact key

theorem heq_comp_whiskerLeft_comp {S T : b ⟶ c} {P : a ⟶ b} (θ : S ⟶ T) {U V W Z : a ⟶ c}
    (φ : U ⟶ V) (η : V ⟶ W) (ψ : W ⟶ Z) (hU : U = P ≫ S) (hV : V = P ≫ 𝟙 b ≫ S)
    (hW : W = P ≫ 𝟙 b ≫ T) (hZ : Z = P ≫ T) (hφ : φ ≍ (ρ_ P).inv ▷ S)
    (hη : η ≍ P ◁ (𝟙 b ◁ θ)) (hψ : ψ ≍ (ρ_ P).hom ▷ T) :
    φ ≫ η ≫ ψ ≍ P ◁ θ := by
  subst hU hV hW hZ
  obtain rfl := eq_of_heq hη
  have hφ' : φ = (ρ_ P).inv ▷ S ≫ eqToHom (assoc _ _ _) := by
    rw [(conj_eqToHom_iff_heq' _ _ rfl (assoc _ _ _)).2 hφ, eqToHom_refl, Category.id_comp]
  have hψ' : ψ = eqToHom (assoc _ _ _).symm ≫ (ρ_ P).hom ▷ T := by
    rw [(conj_eqToHom_iff_heq' _ _ (assoc _ _ _).symm rfl).2 hψ, eqToHom_refl, Category.comp_id]
  subst hφ' hψ'
  have key : (ρ_ P).inv ▷ S ≫ (α_ _ _ _).hom ≫ P ◁ (𝟙 b ◁ θ) ≫ (α_ _ _ _).inv ≫
      (ρ_ P).hom ▷ T = P ◁ θ := by
    bicategory
  rw [← key]
  simp only [Category.assoc]
  rfl

theorem leftUnitor_hom_heq {f f' : a ⟶ b} (h : f = f') : (λ_ f).hom ≍ (λ_ f').hom := by
  subst h; rfl

theorem leftUnitor_inv_heq {f f' : a ⟶ b} (h : f = f') : (λ_ f).inv ≍ (λ_ f').inv := by
  subst h; rfl

theorem leftUnitor_id_whiskerRight_heq (f : a ⟶ b) : (λ_ (𝟙 a)).hom ▷ f ≍ 𝟙 a ◁ (λ_ f).hom := by
  have key : (λ_ (𝟙 a)).hom ▷ f = (α_ _ _ _).hom ≫ 𝟙 a ◁ (λ_ f).hom := by bicategory
  refine (conj_eqToHom_iff_heq' _ _ (assoc _ _ _) rfl).1 ?_
  rw [eqToHom_refl, Category.comp_id]
  exact key

theorem leftUnitor_inv_id_whiskerRight_heq (f : a ⟶ b) :
    (λ_ (𝟙 a)).inv ▷ f ≍ 𝟙 a ◁ (λ_ f).inv := by
  have key : (λ_ (𝟙 a)).inv ▷ f = 𝟙 a ◁ (λ_ f).inv ≫ (α_ _ _ _).inv := by bicategory
  refine (conj_eqToHom_iff_heq' _ _ rfl (assoc _ _ _).symm).1 ?_
  rw [eqToHom_refl, Category.id_comp]
  exact key

theorem rightUnitor_id_comp_heq (f : a ⟶ b) : (ρ_ (𝟙 a ≫ f)).hom ≍ 𝟙 a ◁ (ρ_ f).hom := by
  have key : (ρ_ (𝟙 a ≫ f)).hom = (α_ _ _ _).hom ≫ 𝟙 a ◁ (ρ_ f).hom := by bicategory
  refine (conj_eqToHom_iff_heq' _ _ (assoc _ _ _) rfl).1 ?_
  rw [eqToHom_refl, Category.comp_id]
  exact key

theorem rightUnitor_inv_id_comp_heq (f : a ⟶ b) : (ρ_ (𝟙 a ≫ f)).inv ≍ 𝟙 a ◁ (ρ_ f).inv := by
  have key : (ρ_ (𝟙 a ≫ f)).inv = 𝟙 a ◁ (ρ_ f).inv ≫ (α_ _ _ _).inv := by bicategory
  refine (conj_eqToHom_iff_heq' _ _ rfl (assoc _ _ _).symm).1 ?_
  rw [eqToHom_refl, Category.id_comp]
  exact key

theorem comp_whiskerLeft_heq {d : RoundBicat X n} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d}
    (η : h ⟶ h') : (f ≫ g) ◁ η ≍ f ◁ g ◁ η := by
  rw [Bicategory.comp_whiskerLeft]
  exact (conj_eqToHom_iff_heq' _ _ (assoc f g h) (assoc f g h').symm).1 rfl

end Whisker

end RoundBicat

namespace Layered

open FreeBicategory

namespace Signature.PathInterp

variable {S : Signature.{v}} {X : DiagSet.{u}} (I : S.PathInterp X)

noncomputable def obj (x : S.Pt) : RoundBicat X 0 :=
  ⟨cellRound (I.point x), dimension_atomPoint⟩

noncomputable def edgeHom (e : S.Ed) : I.obj (S.edgeSource e) ⟶ I.obj (S.edgeTarget e) :=
  RoundBicat.Arrow.hom ⟨cellRound (I.edge e).2, HasBdry.of_dim_eq dimension_atomPoint
    (I.hasRoundType_edge e).dim_eq dimension_atomPoint dimension_atomPoint
    (I.hasRoundType_edge e).source (I.hasRoundType_edge e).target⟩

noncomputable def roundPrefunctor : Prefunctor S.GenQuiver (RoundBicat X 0) :=
  S.mkPrefunctor I.obj I.edgeHom

noncomputable abbrev roundLabel : Prefunctor S.PathQuiver (RoundBicat X 0) :=
  S.freePrefunctor ⋙q (lift I.roundPrefunctor).toPrefunctor

theorem mem_roundLabel {x y : S.Pt} (e : Edge S.Pt S.Ed) (h : S.src e = x ∧ S.tgt e = y) :
    (I.roundLabel.map (X := x) (Y := y) ⟨e, h⟩).Mem (I.ofEdge e) := by
  obtain ⟨rfl, rfl⟩ := h
  cases e with
  | gen g => exact (RoundBicat.Arrow.mem_hom _ _).2 (.refl _)
  | unit z => exact RoundBicat.Hom.mem_id (I.obj z)

variable [DecidableEq S.Pt]

theorem mem_pathComp_comp {a x : S.Pt} {P : Quiver.Path (V := S.PathQuiver) a x}
    {m : PastingDiagram X} (hm : (pathComp I.roundLabel P).Mem m) (hsp : I.Spans m a x) :
    ∀ {p : List (Edge S.Pt S.Ed)} {y : S.Pt} (h : S.walk x p = some y),
      (pathComp I.roundLabel (P.comp (S.toPath p h))).Mem (I.whisker true p m)
  | [], y, h => by
    obtain rfl : x = y := Option.some.inj h
    exact hm
  | e :: p, y, h => by
    obtain ⟨he, h'⟩ := S.walk_cons_eq_some.1 h
    have hP : P.comp (S.toPath (e :: p) h) =
        (P.cons (⟨e, he, rfl⟩ : {e' : Edge S.Pt S.Ed // S.src e' = x ∧ S.tgt e' = S.tgt e})).comp
          (S.toPath p h') :=
      (Quiver.Path.comp_assoc (V := S.PathQuiver) P _ _).symm
    have hs := I.spans_of_hasRoundType (I.hasRoundType_ofEdge e)
    rw [he] at hs
    have hpe : m.Pastable (I.ofEdge e) 0 := hsp.pastable hs
    have ih := mem_pathComp_comp (P := P.cons ⟨e, he, rfl⟩)
      (RoundBicat.Hom.Mem.comp hm (I.mem_roundLabel e _) hpe) (hsp.paste hs hpe) h'
    have ea := I.whisker_append true hsp (w₁ := [e]) (w₂ := p) (c := y)
      (by rw [cond_true, cond_true, cond_true, List.singleton_append]; exact h)
    rw [cond_true, List.singleton_append] at ea
    have eb : (I.whisker true p (m.paste (I.ofEdge e) 0 hpe)).Equiv
        (I.whisker true p (I.whisker true [e] m)) :=
      I.whisker_equiv true (hsp.paste hs hpe)
        (PastingDiagram.equiv_of_eq (pasteOr_of hpe).symm) h'
    rw [hP]
    exact ih.of_equiv (eb.trans ea.symm)

theorem mem_pathComp {p : List (Edge S.Pt S.Ed)} {x y : S.Pt} (h : S.walk x p = some y) :
    (pathComp I.roundLabel (S.toPath p h)).Mem
      (I.whisker true p (PastingDiagram.ofCell (I.point x)).unit) := by
  have hm := I.mem_pathComp_comp (a := x) (P := .nil) (RoundBicat.Hom.mem_id (I.obj x))
    (I.spans_of_hasRoundType (hasRoundType_unit (cellRound (I.point x)))) h
  rw [← Quiver.Path.nil_comp (S.toPath p h)]
  exact hm

noncomputable def pathHom {p : List (Edge S.Pt S.Ed)} {x y : S.Pt}
    (hp : S.pathEnds p = some (x, y)) : I.obj x ⟶ I.obj y :=
  RoundBicat.Arrow.hom ⟨I.pathRound p (S.isPath_of_pathEnds hp), HasBdry.of_dim_eq
    dimension_atomPoint (I.hasRoundType_path _ hp).dim_eq dimension_atomPoint dimension_atomPoint
    (I.hasRoundType_path _ hp).source (I.hasRoundType_path _ hp).target⟩

theorem mem_pathHom {p : List (Edge S.Pt S.Ed)} {x y : S.Pt} (hp : S.pathEnds p = some (x, y))
    (hne : p ≠ []) : (I.pathHom hp).Mem (I.path p hne) :=
  (RoundBicat.Arrow.mem_hom _ _).2 (.refl _)

theorem pathHom_congr {p p' : List (Edge S.Pt S.Ed)} {x y : S.Pt} (e : p = p')
    (hp : S.pathEnds p = some (x, y)) (hp' : S.pathEnds p' = some (x, y)) :
    I.pathHom hp = I.pathHom hp' := by
  subst e
  rfl

theorem pathHom_append {p q : List (Edge S.Pt S.Ed)} {x y z : S.Pt}
    (hp : S.pathEnds p = some (x, y)) (hq : S.pathEnds q = some (y, z))
    (hpq : S.pathEnds (p ++ q) = some (x, z)) :
    I.pathHom hp ≫ I.pathHom hq = I.pathHom hpq := by
  obtain ⟨h, e⟩ := I.equiv_path_append (S.isPath_of_pathEnds hp).ne_nil
    (S.isPath_of_pathEnds hq).ne_nil (S.isPath_of_pathEnds hpq)
  exact RoundBicat.Hom.eq_of_mem (RoundBicat.Hom.Mem.comp (I.mem_pathHom hp _)
    (I.mem_pathHom hq _) h) ((I.mem_pathHom hpq _).of_equiv e)

noncomputable def pathCls {u v : List (Edge S.Pt S.Ed)} {m n : S.Pt}
    (hu : S.pathEnds u = some (m, n)) (hv : S.pathEnds v = some (m, n)) {y : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound v (S.isPath_of_pathEnds hv))) :
    I.pathHom hu ⟶ I.pathHom hv :=
  RoundBicat.homMk (RoundBicat.Cell.ofRounding (n := 0) y
    (hy.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hu))))
    ((I.mem_pathHom hu _).of_equiv
      (hy.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hu)) false).symm)
    ((I.mem_pathHom hv _).of_equiv
      (hy.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hu)) true).symm))

theorem pathCls_heq {u v u' v' : List (Edge S.Pt S.Ed)} {m n : S.Pt}
    {hu : S.pathEnds u = some (m, n)} {hv : S.pathEnds v = some (m, n)}
    {hu' : S.pathEnds u' = some (m, n)} {hv' : S.pathEnds v' = some (m, n)}
    (huu : u = u') (hvv : v = v') {y y' : PastingDiagram X} (e : y.Equiv y')
    (hy : HasRoundType y (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound v (S.isPath_of_pathEnds hv)))
    (hy' : HasRoundType y' (I.pathRound u' (S.isPath_of_pathEnds hu'))
      (I.pathRound v' (S.isPath_of_pathEnds hv'))) :
    I.pathCls hu hv hy ≍ I.pathCls hu' hv' hy' :=
  RoundBicat.homMk_ofRounding_heq (I.pathHom_congr huu hu hu') (I.pathHom_congr hvv hv hv') e _ _ _
    _ _ _

theorem pathCls_comp {u v w : List (Edge S.Pt S.Ed)} {m n : S.Pt}
    (hu : S.pathEnds u = some (m, n)) (hv : S.pathEnds v = some (m, n))
    (hw : S.pathEnds w = some (m, n)) {y z yz : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound v (S.isPath_of_pathEnds hv)))
    (hz : HasRoundType z (I.pathRound v (S.isPath_of_pathEnds hv))
      (I.pathRound w (S.isPath_of_pathEnds hw)))
    (hyz : HasRoundType yz (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound w (S.isPath_of_pathEnds hw)))
    (hp : y.Pastable z 1) (e : yz.Equiv (y.paste z 1 hp)) :
    I.pathCls hu hv hy ≫ I.pathCls hv hw hz = I.pathCls hu hw hyz := by
  have hd := I.dim_path (S.isPath_of_pathEnds hu)
  refine (RoundBicat.homMk_ofRounding_comp (n := 0) _ _ _ _ _ _ hp
    ((dim_eq_of_equiv e).symm.trans (hyz.dim_eq.trans (congrArg (· + 1) hd)))
    ((I.mem_pathHom hu _).of_equiv
      ((hyz.equiv_boundary_cond hd false).symm.trans (e.boundary 1 false)))
    ((I.mem_pathHom hw _).of_equiv
      ((hyz.equiv_boundary_cond hd true).symm.trans (e.boundary 1 true)))).trans ?_
  exact RoundBicat.homMk_ofRounding_congr e.symm _ _ _ _ _ _

theorem pathCls_unit {u : List (Edge S.Pt S.Ed)} {m n : S.Pt} (hu : S.pathEnds u = some (m, n))
    (hy : HasRoundType (I.path u (S.isPath_of_pathEnds hu).ne_nil).unit
      (I.pathRound u (S.isPath_of_pathEnds hu)) (I.pathRound u (S.isPath_of_pathEnds hu))) :
    I.pathCls hu hu hy = 𝟙 _ :=
  RoundBicat.homMk_ofRounding_unit (I.mem_pathHom hu _) _ _ _

theorem pathCls_eq_id {u : List (Edge S.Pt S.Ed)} {m n : S.Pt} (hu : S.pathEnds u = some (m, n))
    {y : PastingDiagram X} (e : y.Equiv (I.path u (S.isPath_of_pathEnds hu).ne_nil).unit)
    (hy : HasRoundType y (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound u (S.isPath_of_pathEnds hu))) :
    I.pathCls hu hu hy = 𝟙 _ :=
  eq_of_heq ((I.pathCls_heq rfl rfl e hy (hasRoundType_unit (I.pathRound u _))).trans
    (heq_of_eq (I.pathCls_unit hu _)))

theorem pathComp_comp_toPath {a x : S.Pt} {P : Quiver.Path (V := S.PathQuiver) a x}
    {m : PastingDiagram X} (hm : (pathComp I.roundLabel P).Mem m) (hsp : I.Spans m a x)
    {p : List (Edge S.Pt S.Ed)} {y : S.Pt} (h : S.walk x p = some y)
    (hp : S.pathEnds p = some (x, y)) :
    pathComp I.roundLabel (P.comp (S.toPath p h)) = pathComp I.roundLabel P ≫ I.pathHom hp := by
  obtain _ | ⟨e, p'⟩ := p
  · exact absurd hp (by simp only [pathEnds_nil, reduceCtorEq, not_false_eq_true])
  have hq := I.spans_of_hasRoundType (I.hasRoundType_path (List.cons_ne_nil e p') hp)
  have hpq : m.Pastable (I.path (e :: p') (List.cons_ne_nil e p')) 0 := hsp.pastable hq
  refine RoundBicat.Hom.eq_of_mem (I.mem_pathComp_comp hm hsp h) ?_
  rw [show I.whisker true (e :: p') m = m.paste (I.path (e :: p') (List.cons_ne_nil e p')) 0 hpq
    from pasteOr_of hpq]
  exact RoundBicat.Hom.Mem.comp hm (I.mem_pathHom hp _) hpq

theorem pathComp_toPath {p : List (Edge S.Pt S.Ed)} {x y : S.Pt} (h : S.walk x p = some y)
    (hp : S.pathEnds p = some (x, y)) :
    pathComp I.roundLabel (S.toPath p h) = 𝟙 _ ≫ I.pathHom hp := by
  rw [← Quiver.Path.nil_comp (S.toPath p h)]
  exact I.pathComp_comp_toPath (a := x) (P := .nil) (RoundBicat.Hom.mem_id (I.obj x))
    (I.spans_of_hasRoundType (hasRoundType_unit (cellRound (I.point x)))) h hp

theorem pathCompCompIso_toPath_heq {a x : S.Pt} {P : Quiver.Path (V := S.PathQuiver) a x}
    {m : PastingDiagram X} (hm : (pathComp I.roundLabel P).Mem m) (hsp : I.Spans m a x)
    (p : List (Edge S.Pt S.Ed)) {y : S.Pt} (h : S.walk x p = some y)
    (hp : S.pathEnds p = some (x, y)) :
    (pathCompCompIso I.roundLabel P (S.toPath p h)).hom ≍
      (ρ_ (pathComp I.roundLabel P)).inv ▷ I.pathHom hp := by
  induction p using List.reverseRecOn generalizing y with
  | nil => exact absurd hp (by simp only [pathEnds_nil, reduceCtorEq, not_false_eq_true])
  | append_singleton p e ih =>
    obtain ⟨z, hz, he⟩ := S.walk_append_eq_some h
    obtain ⟨hsrc, hy⟩ := S.walk_cons_eq_some.1 he
    obtain rfl : S.tgt e = y := Option.some.inj hy
    have hQ : S.toPath (p ++ [e]) h = (S.toPath p hz).cons
        (⟨e, hsrc, rfl⟩ : {e' : Edge S.Pt S.Ed // S.src e' = z ∧ S.tgt e' = S.tgt e}) :=
      S.toPath_append h hz he
    rw [hQ]
    refine (heq_of_eq (pathCompCompIso_cons_hom I.roundLabel P (S.toPath p hz) _)).trans ?_
    rw [RoundBicat.associator_hom]
    refine (comp_eqToHom_heq _ _).trans ?_
    obtain _ | ⟨e₀, p₀⟩ := p
    · obtain rfl : x = z := Option.some.inj hz
      exact whiskerRight_heq rfl rfl (RoundBicat.Hom.eq_of_mem (I.mem_roundLabel e _)
        (I.mem_pathHom hp (List.cons_ne_nil _ _)))
        (heq_of_eq (congrArg Iso.hom (pathCompCompIso_comp_nil I.roundLabel P)))
    · have hp₀ : S.pathEnds (e₀ :: p₀) = some (x, z) :=
        S.pathEnds_eq_some_iff.2 ⟨List.cons_ne_nil _ _, hz⟩
      have hH : I.pathHom hp₀ ≫ I.roundLabel.map ⟨e, hsrc, rfl⟩ = I.pathHom hp := by
        obtain ⟨hpe, ee⟩ := I.equiv_path_append (List.cons_ne_nil e₀ p₀) (List.cons_ne_nil e [])
          (S.isPath_of_pathEnds hp)
        exact RoundBicat.Hom.eq_of_mem (RoundBicat.Hom.Mem.comp (I.mem_pathHom hp₀ _)
          (I.mem_roundLabel e _) hpe) ((I.mem_pathHom hp _).of_equiv ee)
      refine (whiskerRight_heq (I.pathComp_comp_toPath hm hsp hz hp₀) ?_ rfl
        (ih hz hp₀)).trans ?_
      · rw [I.pathComp_toPath hz hp₀]
        exact (RoundBicat.assoc _ _ _).symm
      have key : (ρ_ (pathComp I.roundLabel P)).inv ▷
          (I.pathHom hp₀ ≫ I.roundLabel.map ⟨e, hsrc, rfl⟩) =
            eqToHom (RoundBicat.assoc _ _ _).symm ≫
              (ρ_ (pathComp I.roundLabel P)).inv ▷ I.pathHom hp₀ ▷ I.roundLabel.map ⟨e, hsrc, rfl⟩ ≫
                eqToHom (RoundBicat.assoc _ _ _) :=
        whiskerRight_comp _ _ _
      exact ((conj_eqToHom_iff_heq' _ _ _ _).1 key).symm.trans
        (whiskerRight_heq rfl rfl hH HEq.rfl)

theorem spans_whisker_unit {p : List (Edge S.Pt S.Ed)} {x y : S.Pt} (h : S.walk x p = some y) :
    I.Spans (I.whisker true p (PastingDiagram.ofCell (I.point x)).unit) x y :=
  (I.spans_of_hasRoundType (hasRoundType_unit (cellRound (I.point x)))).whisker true (c := y) h

theorem pathComp_toPath_comp_toPath {s R : List (Edge S.Pt S.Ed)} {m n b : S.Pt}
    (hs : S.walk m s = some n) (hR : S.walk n R = some b) (hR' : S.pathEnds R = some (n, b)) :
    pathComp I.roundLabel ((S.toPath s hs).comp (S.toPath R hR)) =
      pathComp I.roundLabel (S.toPath s hs) ≫ I.pathHom hR' :=
  I.pathComp_comp_toPath (I.mem_pathComp hs) (I.spans_whisker_unit hs) hR hR'

theorem pathCompCompIso_toPath_toPath_heq {s R : List (Edge S.Pt S.Ed)} {m n b : S.Pt}
    (hs : S.walk m s = some n) (hR : S.walk n R = some b) (hR' : S.pathEnds R = some (n, b)) :
    (pathCompCompIso I.roundLabel (S.toPath s hs) (S.toPath R hR)).hom ≍
      (ρ_ (pathComp I.roundLabel (S.toPath s hs))).inv ▷ I.pathHom hR' :=
  I.pathCompCompIso_toPath_heq (I.mem_pathComp hs) (I.spans_whisker_unit hs) R hR hR'

theorem pathCompCompIso_whiskerRight_heq {s t R : List (Edge S.Pt S.Ed)} {m n b : S.Pt}
    (hs : S.walk m s = some n) (ht : S.walk m t = some n) (hs' : S.pathEnds s = some (m, n))
    (ht' : S.pathEnds t = some (m, n)) (hR : S.walk n R = some b) {y : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound s (S.isPath_of_pathEnds hs'))
      (I.pathRound t (S.isPath_of_pathEnds ht')))
    {η : pathComp I.roundLabel (S.toPath s hs) ⟶ pathComp I.roundLabel (S.toPath t ht)}
    (hη : η ≍ 𝟙 _ ◁ I.pathCls hs' ht' hy) :
    (pathCompCompIso I.roundLabel (S.toPath s hs) (S.toPath R hR)).hom ≫
        η ▷ pathComp I.roundLabel (S.toPath R hR) ≫
          (pathCompCompIso I.roundLabel (S.toPath t ht) (S.toPath R hR)).inv ≍
      𝟙 _ ◁ I.pathCls (S.pathEnds_whisker true hs' (c := b) hR)
        (S.pathEnds_whisker true ht' (c := b) hR) (I.hasRoundType_whisker true hs' ht' hy hR) := by
  obtain _ | ⟨e, R'⟩ := R
  · obtain rfl : n = b := Option.some.inj hR
    have h₀ : (pathCompCompIso I.roundLabel (S.toPath s hs) (S.toPath [] hR)).hom ≫
        η ▷ pathComp I.roundLabel (S.toPath [] hR) ≫
          (pathCompCompIso I.roundLabel (S.toPath t ht) (S.toPath [] hR)).inv = η := by
      have e₁ : (pathCompCompIso I.roundLabel (S.toPath s hs) (S.toPath [] hR)).hom =
          (ρ_ _).inv := congrArg Iso.hom (pathCompCompIso_comp_nil I.roundLabel (S.toPath s hs))
      have e₂ : (pathCompCompIso I.roundLabel (S.toPath t ht) (S.toPath [] hR)).inv =
          (ρ_ _).hom := congrArg Iso.inv (pathCompCompIso_comp_nil I.roundLabel (S.toPath t ht))
      rw [e₁, e₂]
      exact (whiskerRight_id_symm η).symm
    rw [h₀]
    refine hη.trans (whiskerLeft_heq rfl ?_ ?_ (I.pathCls_heq ?_ ?_ (.refl _) _ _))
    · exact I.pathHom_congr (List.append_nil s).symm _ _
    · exact I.pathHom_congr (List.append_nil t).symm _ _
    · exact (List.append_nil s).symm
    · exact (List.append_nil t).symm
  · have hR'' : S.pathEnds (e :: R') = some (n, b) :=
      S.pathEnds_eq_some_iff.2 ⟨List.cons_ne_nil _ _, hR⟩
    have es := I.pathComp_toPath hs hs'
    have et := I.pathComp_toPath ht ht'
    have eR := I.pathComp_toPath hR hR''
    refine (RoundBicat.heq_comp_whiskerRight_comp (H := I.pathHom hR'') (I.pathCls hs' ht' hy)
      _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      ?_).trans ?_
    · exact (I.pathComp_toPath_comp_toPath hs hR hR'').trans (congrArg (· ≫ _) es)
    · exact (congrArg₂ (· ≫ ·) es eR).trans (RoundBicat.assoc _ _ _).symm
    · exact congrArg₂ (· ≫ ·) et eR
    · exact (I.pathComp_toPath_comp_toPath ht hR hR'').trans (congrArg (· ≫ _) et)
    · exact (I.pathCompCompIso_toPath_toPath_heq hs hR hR'').trans
        (whiskerRight_heq es (congrArg (· ≫ 𝟙 _) es) rfl (RoundBicat.rightUnitor_inv_heq es))
    · exact whiskerRight_heq es et eR hη
    · exact Iso.inv_heq_inv (e' := whiskerRightIso (ρ_ (𝟙 _ ≫ I.pathHom ht')).symm (I.pathHom hR''))
        ((I.pathComp_toPath_comp_toPath ht hR hR'').trans (congrArg (· ≫ _) et))
        ((congrArg₂ (· ≫ ·) et eR).trans (RoundBicat.assoc _ _ _).symm)
        ((I.pathCompCompIso_toPath_toPath_heq ht hR hR'').trans
          (whiskerRight_heq et (congrArg (· ≫ 𝟙 _) et) rfl (RoundBicat.rightUnitor_inv_heq et)))
    have hsR := S.pathEnds_whisker true hs' (c := b) hR
    have htR := S.pathEnds_whisker true ht' (c := b) hR
    refine whiskerLeft_heq rfl (I.pathHom_append hs' hR'' hsR) (I.pathHom_append ht' hR'' htR) ?_
    have hyR := I.hasRoundType_whisker true hs' ht' hy hR
    have hp : y.Pastable (I.path (e :: R') (List.cons_ne_nil _ _)) 0 :=
      ((I.spans_of_hasRoundType (I.hasRoundType_path _ hs')).of_hasRoundType hy).pastable
        (I.spans_of_hasRoundType (I.hasRoundType_path _ hR''))
    have ew : I.whisker true (e :: R') y = y.paste _ 0 hp := pasteOr_of hp
    rw [ew] at hyR
    have hd := hyR.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hsR)))
    have ms := (I.mem_pathHom hsR _).of_equiv
      (hyR.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hsR)) false).symm
    have mt := (I.mem_pathHom htR _).of_equiv
      (hyR.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hsR)) true).symm
    rw [← I.pathHom_append hs' hR'' hsR] at ms
    rw [← I.pathHom_append ht' hR'' htR] at mt
    rw [pathCls, RoundBicat.homMk_ofRounding_whiskerRight (I.mem_pathHom hR'' _) _ _ _ hp hd ms mt]
    exact RoundBicat.homMk_ofRounding_heq (I.pathHom_append hs' hR'' hsR)
      (I.pathHom_append ht' hR'' htR) (PastingDiagram.equiv_of_eq ew.symm) _ _ _ _ _ _

theorem pathCompCompIso_whiskerLeft_heq {Lst M M' : List (Edge S.Pt S.Ed)} {a m b : S.Pt}
    (hL : S.walk a Lst = some m) (hM : S.walk m M = some b) (hM' : S.walk m M' = some b)
    (hMe : S.pathEnds M = some (m, b)) (hMe' : S.pathEnds M' = some (m, b))
    {Q Q' : Quiver.Path (V := S.PathQuiver) m b} (hQ : Q = S.toPath M hM)
    (hQ' : Q' = S.toPath M' hM') {y : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound M (S.isPath_of_pathEnds hMe))
      (I.pathRound M' (S.isPath_of_pathEnds hMe')))
    {ζ : pathComp I.roundLabel Q ⟶ pathComp I.roundLabel Q'}
    (hζ : ζ ≍ 𝟙 _ ◁ I.pathCls hMe hMe' hy) :
    (pathCompCompIso I.roundLabel (S.toPath Lst hL) Q).hom ≫
        pathComp I.roundLabel (S.toPath Lst hL) ◁ ζ ≫
          (pathCompCompIso I.roundLabel (S.toPath Lst hL) Q').inv ≍
      𝟙 _ ◁ I.pathCls (S.pathEnds_whisker false hMe (c := a) hL)
        (S.pathEnds_whisker false hMe' (c := a) hL)
        (I.hasRoundType_whisker false hMe hMe' hy (c := a) hL) := by
  subst hQ hQ'
  obtain _ | ⟨e, L'⟩ := Lst
  · obtain rfl : a = m := Option.some.inj hL
    exact (pathCompCompIso_nil_whiskerLeft_heq I.roundLabel ζ).trans hζ
  · have hL' : S.pathEnds (e :: L') = some (a, m) :=
      S.pathEnds_eq_some_iff.2 ⟨List.cons_ne_nil _ _, hL⟩
    have eL := I.pathComp_toPath hL hL'
    have eM := I.pathComp_toPath hM hMe
    have eM' := I.pathComp_toPath hM' hMe'
    refine (RoundBicat.heq_comp_whiskerLeft_comp (P := pathComp I.roundLabel (S.toPath _ hL))
      (I.pathCls hMe hMe' hy) _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
    · exact I.pathComp_comp_toPath (I.mem_pathComp hL) (I.spans_whisker_unit hL) hM hMe
    · exact congrArg (_ ≫ ·) eM
    · exact congrArg (_ ≫ ·) eM'
    · exact I.pathComp_comp_toPath (I.mem_pathComp hL) (I.spans_whisker_unit hL) hM' hMe'
    · exact I.pathCompCompIso_toPath_heq (I.mem_pathComp hL) (I.spans_whisker_unit hL) M hM hMe
    · exact whiskerLeft_heq rfl eM eM' hζ
    · exact Iso.inv_heq_inv
        (e' := whiskerRightIso (ρ_ (pathComp I.roundLabel (S.toPath _ hL))).symm (I.pathHom hMe'))
        (I.pathComp_comp_toPath (I.mem_pathComp hL) (I.spans_whisker_unit hL) hM' hMe')
        ((congrArg (_ ≫ ·) eM').trans (RoundBicat.assoc _ _ _).symm)
        (I.pathCompCompIso_toPath_heq (I.mem_pathComp hL) (I.spans_whisker_unit hL) M' hM' hMe')
    have hLM := S.pathEnds_whisker false hMe (c := a) hL
    have hLM' := S.pathEnds_whisker false hMe' (c := a) hL
    refine (whiskerLeft_heq eL rfl rfl HEq.rfl).trans ((RoundBicat.comp_whiskerLeft_heq _ _ _).trans
      (whiskerLeft_heq rfl (I.pathHom_append hL' hMe hLM) (I.pathHom_append hL' hMe' hLM') ?_))
    have hyL := I.hasRoundType_whisker false hMe hMe' hy (c := a) hL
    have hp : (I.path (e :: L') (List.cons_ne_nil _ _)).Pastable y 0 :=
      (I.spans_of_hasRoundType (I.hasRoundType_path _ hL')).pastable
        ((I.spans_of_hasRoundType (I.hasRoundType_path _ hMe)).of_hasRoundType hy)
    have ew : I.whisker false (e :: L') y =
        (I.path (e :: L') (List.cons_ne_nil _ _)).paste y 0 hp :=
      pasteOr_of hp
    rw [ew] at hyL
    have hd := hyL.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hLM)))
    have ms := (I.mem_pathHom hLM (S.isPath_of_pathEnds hLM).ne_nil).of_equiv
      (hyL.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hLM)) false).symm
    have mt := (I.mem_pathHom hLM' (S.isPath_of_pathEnds hLM').ne_nil).of_equiv
      (hyL.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hLM)) true).symm
    rw [← I.pathHom_append hL' hMe hLM] at ms
    rw [← I.pathHom_append hL' hMe' hLM'] at mt
    refine (heq_of_eq (RoundBicat.whiskerLeft_homMk_ofRounding (I.mem_pathHom hL' _) _ _ _ hp hd
      ms mt)).trans ?_
    exact RoundBicat.homMk_ofRounding_heq (I.pathHom_append hL' hMe hLM)
      (I.pathHom_append hL' hMe' hLM') (PastingDiagram.equiv_of_eq ew.symm) _ _ _ _ _ _

theorem pathWhisker_heq {L s t R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hL : S.walk a L = some m) (hs : S.walk m s = some n) (ht : S.walk m t = some n)
    (hs' : S.pathEnds s = some (m, n)) (ht' : S.pathEnds t = some (m, n))
    (hR : S.walk n R = some b) {y : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound s (S.isPath_of_pathEnds hs'))
      (I.pathRound t (S.isPath_of_pathEnds ht')))
    {η : pathComp I.roundLabel (S.toPath s hs) ⟶ pathComp I.roundLabel (S.toPath t ht)}
    (hη : η ≍ 𝟙 _ ◁ I.pathCls hs' ht' hy) :
    pathWhisker I.roundLabel (S.toPath L hL) η (S.toPath R hR) ≍
      𝟙 _ ◁ I.pathCls
        (S.pathEnds_whisker false (S.pathEnds_whisker true hs' (c := b) hR) (c := a) hL)
        (S.pathEnds_whisker false (S.pathEnds_whisker true ht' (c := b) hR) (c := a) hL)
        (I.hasRoundType_whisker false (S.pathEnds_whisker true hs' (c := b) hR)
          (S.pathEnds_whisker true ht' (c := b) hR) (I.hasRoundType_whisker true hs' ht' hy hR)
          (c := a) hL) := by
  have hsR : S.walk m (s ++ R) = some b := by rw [S.walk_append, hs, Option.bind_some, hR]
  have htR : S.walk m (t ++ R) = some b := by rw [S.walk_append, ht, Option.bind_some, hR]
  exact I.pathCompCompIso_whiskerLeft_heq hL hsR htR _ _ (S.toPath_append hsR hs hR).symm
    (S.toPath_append htR ht hR).symm _ (I.pathCompCompIso_whiskerRight_heq hs ht hs' ht' hR hy hη)

theorem pathCls_eq_homMk {u v : List (Edge S.Pt S.Ed)} {m n : S.Pt}
    (hu : S.pathEnds u = some (m, n)) (hv : S.pathEnds v = some (m, n)) {y : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound v (S.isPath_of_pathEnds hv)))
    (t : RoundBicat.Cell (I.pathHom hu) (I.pathHom hv)) (ht : t.diag.toPastingDiagram = y) :
    I.pathCls hu hv hy = RoundBicat.homMk t := by
  subst ht
  exact RoundBicat.homMk_ofRounding_diag t

noncomputable def pathCell {u v : List (Edge S.Pt S.Ed)} {m n : S.Pt}
    (hu : S.pathEnds u = some (m, n)) (hv : S.pathEnds v = some (m, n)) {y : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound v (S.isPath_of_pathEnds hv))) (hr : y.IsRound) {f g : I.obj m ⟶ I.obj n}
    (hf : I.pathHom hu = f) (hg : I.pathHom hv = g) : RoundBicat.Cell f g where
  diag := ⟨y, hr⟩
  dim_diag := hy.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hu)))
  source := hf ▸ (I.mem_pathHom hu _).of_equiv
    (hy.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hu)) false).symm
  target := hg ▸ (I.mem_pathHom hv _).of_equiv
    (hy.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hu)) true).symm

theorem pathCls_heq_homMk_pathCell {u v : List (Edge S.Pt S.Ed)} {m n : S.Pt}
    (hu : S.pathEnds u = some (m, n)) (hv : S.pathEnds v = some (m, n)) {y : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound v (S.isPath_of_pathEnds hv))) (hr : y.IsRound) {f g : I.obj m ⟶ I.obj n}
    (hf : I.pathHom hu = f) (hg : I.pathHom hv = g) :
    I.pathCls hu hv hy ≍ RoundBicat.homMk (I.pathCell hu hv hy hr hf hg) := by
  subst hf hg
  exact heq_of_eq (I.pathCls_eq_homMk hu hv hy _ rfl)

theorem pathCls_reverse_heq {u v : List (Edge S.Pt S.Ed)} {m n : S.Pt}
    (hu : S.pathEnds u = some (m, n)) (hv : S.pathEnds v = some (m, n)) {y : PastingDiagram X}
    (hd : y.IsDegenerate) (hr : y.IsRound)
    (hy : HasRoundType y (I.pathRound u (S.isPath_of_pathEnds hu))
      (I.pathRound v (S.isPath_of_pathEnds hv)))
    (hy' : HasRoundType (y.reverse hd) (I.pathRound v (S.isPath_of_pathEnds hv))
      (I.pathRound u (S.isPath_of_pathEnds hu)))
    {A B : I.obj m ⟶ I.obj n} (e : A ≅ B) (hA : I.pathHom hu = A) (hB : I.pathHom hv = B)
    (h : I.pathCls hu hv hy ≍ e.hom) : I.pathCls hv hu hy' ≍ e.inv := by
  subst hA hB
  have h₁ := I.pathCls_eq_homMk hu hv hy (I.pathCell hu hv hy hr rfl rfl) rfl
  have h₂ := I.pathCls_eq_homMk hv hu hy' (I.pathCell hv hu hy' (isRound_reverse hd hr) rfl rfl) rfl
  have hc := RoundBicat.homMk_comp_homMk_reverse (I.pathCell hu hv hy hr rfl rfl) hd
    (I.pathCell hv hu hy' (isRound_reverse hd hr) rfl rfl) rfl
  rw [← h₁, ← h₂, eq_of_heq h] at hc
  exact heq_of_eq (Iso.inv_ext hc).symm

theorem pathHom_unitPath (σ : Bool) (e : Edge S.Pt S.Ed)
    (hse : S.pathEnds [e] = some (S.src e, S.tgt e))
    (hte : S.pathEnds (S.unitPath σ e) = some (S.src e, S.tgt e)) :
    I.pathHom hte = cond σ (I.pathHom hse ≫ 𝟙 _) (𝟙 _ ≫ I.pathHom hse) := by
  have hsp := I.spans_of_hasRoundType (I.hasRoundType_ofEdge e)
  cases σ
  · have hp : (PastingDiagram.ofCell (I.point (S.src e))).unit.Pastable (I.ofEdge e) 0 :=
      (I.spans_of_hasRoundType (hasRoundType_unit (cellRound (I.point (S.src e))))).pastable hsp
    have ep : I.path (S.unitPath false e) (List.cons_ne_nil _ _) =
        (PastingDiagram.ofCell (I.point (S.src e))).unit.paste (I.ofEdge e) 0 hp := pasteOr_of hp
    refine RoundBicat.Hom.eq_of_mem (I.mem_pathHom hte (List.cons_ne_nil _ _)) ?_
    rw [ep]
    exact RoundBicat.Hom.Mem.comp (RoundBicat.Hom.mem_id (I.obj (S.src e)))
      (I.mem_pathHom hse (List.cons_ne_nil _ _)) hp
  · have hp : (I.ofEdge e).Pastable (PastingDiagram.ofCell (I.point (S.tgt e))).unit 0 :=
      hsp.pastable (I.spans_of_hasRoundType (hasRoundType_unit (cellRound (I.point (S.tgt e)))))
    have ep : I.path (S.unitPath true e) (List.cons_ne_nil _ _) =
        (I.ofEdge e).paste (PastingDiagram.ofCell (I.point (S.tgt e))).unit 0 hp := pasteOr_of hp
    refine RoundBicat.Hom.eq_of_mem (I.mem_pathHom hte (List.cons_ne_nil _ _)) ?_
    rw [ep]
    exact RoundBicat.Hom.Mem.comp (I.mem_pathHom hse (List.cons_ne_nil _ _))
      (RoundBicat.Hom.mem_id (I.obj (S.tgt e))) hp

theorem pathCls_edgeUnitor_false_heq (e : Edge S.Pt S.Ed)
    (hse : S.pathEnds [e] = some (S.src e, S.tgt e))
    (hte : S.pathEnds (S.unitPath false e) = some (S.src e, S.tgt e))
    (hy : HasRoundType (I.edgeUnitor false e) (I.pathRound [e] (S.isPath_of_pathEnds hse))
      (I.pathRound (S.unitPath false e) (S.isPath_of_pathEnds hte))) :
    I.pathCls hse hte hy ≍ (λ_ (I.pathHom hse)).inv := by
  refine (I.pathCls_heq_homMk_pathCell hse hte hy (I.isRound_edgeUnitor false e) rfl
    (I.pathHom_unitPath false e hse hte)).trans (heq_of_eq ?_)
  exact (RoundBicat.leftUnitor_inv_eq_homMk_of_equiv (I.mem_pathHom hse (List.cons_ne_nil _ _))
    (by rw [I.dim_path (S.isPath_of_pathEnds hse)]; exact Nat.one_pos)
    (isRound_boundary_of_isRound (I.isRound_path (S.isPath_of_pathEnds hse)) _ false) _
    (.refl _)).symm

theorem pathCls_edgeUnitor_true_heq (e : Edge S.Pt S.Ed)
    (hse : S.pathEnds [e] = some (S.src e, S.tgt e))
    (hte : S.pathEnds (S.unitPath true e) = some (S.src e, S.tgt e))
    (hy : HasRoundType (I.edgeUnitor true e) (I.pathRound (S.unitPath true e)
      (S.isPath_of_pathEnds hte)) (I.pathRound [e] (S.isPath_of_pathEnds hse))) :
    I.pathCls hte hse hy ≍ (ρ_ (I.pathHom hse)).hom := by
  refine (I.pathCls_heq_homMk_pathCell hte hse hy (I.isRound_edgeUnitor true e)
    (I.pathHom_unitPath true e hse hte) rfl).trans (heq_of_eq ?_)
  exact (RoundBicat.rightUnitor_hom_eq_homMk_of_equiv (I.mem_pathHom hse (List.cons_ne_nil _ _))
    (by rw [I.dim_path (S.isPath_of_pathEnds hse)]; exact Nat.one_pos)
    (isRound_boundary_of_isRound (I.isRound_path (S.isPath_of_pathEnds hse)) _ true) _
    (.refl _)).symm

end Signature.PathInterp

namespace Signature.Interp

variable {S : Signature.{v}} [DecidableEq S.Pt] {X : DiagSet.{u}} (I : S.Interp X)
  (hS : S.WellFormed)

theorem pathEnds_cellSource (c : S.Ce) : S.pathEnds (S.cellSource c) = some (S.cellEnds hS c) :=
  (Option.some_get _).symm

theorem pathEnds_cellTarget (c : S.Ce) : S.pathEnds (S.cellTarget c) = some (S.cellEnds hS c) :=
  (hS c).2.symm.trans (Option.some_get _).symm

noncomputable def toRoundBicat : S.BicatInterp hS (RoundBicat X 0) where
  toPrefunctor := I.roundPrefunctor
  cell c := eqToHom (I.pathComp_toPath (S.walk_cellSource hS c) (pathEnds_cellSource hS c)) ≫
    𝟙 _ ◁ I.pathCls (pathEnds_cellSource hS c) (pathEnds_cellTarget hS c)
      (I.hasRoundType_cell c _ _) ≫
    eqToHom (I.pathComp_toPath (S.walk_cellTarget hS c) (pathEnds_cellTarget hS c)).symm

omit [DecidableEq S.Pt] in
theorem pathEnds_cellType_unitor [DecidableEq S.Pt] (k : UnitorKind) (e : Edge S.Pt S.Ed) :
    S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some (S.src e, S.tgt e) := by
  cases k <;> simp [cellType, unitPath, UnitorKind.removes, UnitorKind.side, pathEnds, walk,
    Signature.src, Signature.tgt]

theorem unitorReading_toRoundBicat_heq (k : UnitorKind) (e : Edge S.Pt S.Ed) {a b : S.Pt}
    (hs : S.walk a (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some b)
    (ht : S.walk a (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some b)
    (hse : S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some (a, b))
    (hte : S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some (a, b))
    (hy : HasRoundType (I.unitorDiagram k e) (I.pathRound _ (S.isPath_of_pathEnds hse))
      (I.pathRound _ (S.isPath_of_pathEnds hte))) :
    (I.toRoundBicat hS).unitorReading k e hs ht ≍ 𝟙 _ ◁ I.pathCls hse hte hy := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hse.symm.trans (pathEnds_cellType_unitor k e)))
  have he : S.pathEnds [e] = some (S.src e, S.tgt e) :=
    S.pathEnds_eq_some_iff.2 ⟨List.cons_ne_nil _ _, S.walk_cons_eq_some.2 ⟨rfl, rfl⟩⟩
  have hℓ : I.roundLabel.map ⟨e, rfl, rfl⟩ = I.pathHom he :=
    RoundBicat.Hom.eq_of_mem (I.mem_roundLabel e _) (I.mem_pathHom he (List.cons_ne_nil _ _))
  cases k
  · rw [Signature.BicatInterp.unitorReading_eq _ _ _ hs ht
      ((λ_ (𝟙 _)).hom ▷ S.freePrefunctor.map ⟨e, rfl, rfl⟩)]
    refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
    refine (heq_of_eq (lift_map₂_whiskerRight _ _ _)).trans
      ((RoundBicat.leftUnitor_id_whiskerRight_heq _).trans (whiskerLeft_heq rfl
        ((congrArg (𝟙 _ ≫ ·) hℓ).trans (I.pathHom_unitPath false e he hse).symm)
        (hℓ.trans (I.pathHom_congr rfl he hte)) ?_))
    exact (RoundBicat.leftUnitor_hom_heq hℓ).trans (I.pathCls_reverse_heq he hse
      (I.isDegenerate_edgeUnitor false e) (I.isRound_edgeUnitor false e)
      (I.hasRoundType_edgeUnitor false e) hy (λ_ (I.pathHom he)).symm rfl
      (I.pathHom_unitPath false e he hse) (I.pathCls_edgeUnitor_false_heq e he hse _)).symm
  · rw [Signature.BicatInterp.unitorReading_eq _ _ _ hs ht
      ((λ_ (𝟙 _)).inv ▷ S.freePrefunctor.map ⟨e, rfl, rfl⟩)]
    refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
    refine (heq_of_eq (lift_map₂_whiskerRight _ _ _)).trans
      ((RoundBicat.leftUnitor_inv_id_whiskerRight_heq _).trans (whiskerLeft_heq rfl
        (hℓ.trans (I.pathHom_congr rfl he hse))
        ((congrArg (𝟙 _ ≫ ·) hℓ).trans (I.pathHom_unitPath false e he hte).symm) ?_))
    exact (RoundBicat.leftUnitor_inv_heq hℓ).trans (I.pathCls_edgeUnitor_false_heq e he hte hy).symm
  · rw [Signature.BicatInterp.unitorReading_eq _ _ _ hs ht
      ((ρ_ (𝟙 _ ≫ S.freePrefunctor.map ⟨e, rfl, rfl⟩)).hom)]
    refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
    refine (RoundBicat.rightUnitor_id_comp_heq _).trans (whiskerLeft_heq rfl
      ((congrArg (· ≫ 𝟙 _) hℓ).trans (I.pathHom_unitPath true e he hse).symm)
      (hℓ.trans (I.pathHom_congr rfl he hte)) ?_)
    exact (RoundBicat.rightUnitor_hom_heq hℓ).trans (I.pathCls_edgeUnitor_true_heq e he hse hy).symm
  · rw [Signature.BicatInterp.unitorReading_eq _ _ _ hs ht
      ((ρ_ (𝟙 _ ≫ S.freePrefunctor.map ⟨e, rfl, rfl⟩)).inv)]
    refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
    refine (RoundBicat.rightUnitor_inv_id_comp_heq _).trans (whiskerLeft_heq rfl
      (hℓ.trans (I.pathHom_congr rfl he hse))
      ((congrArg (· ≫ 𝟙 _) hℓ).trans (I.pathHom_unitPath true e he hte).symm) ?_)
    exact (RoundBicat.rightUnitor_inv_heq hℓ).trans (I.pathCls_reverse_heq hte he
      (I.isDegenerate_edgeUnitor true e) (I.isRound_edgeUnitor true e)
      (I.hasRoundType_edgeUnitor true e) hy (ρ_ (I.pathHom he))
      (I.pathHom_unitPath true e he hte) rfl (I.pathCls_edgeUnitor_true_heq e he hte _)).symm

theorem cellReading_toRoundBicat_heq (x : PastingDiagram X) (c : Cell S.Pt S.Ed S.Ce)
    (hc : (S.pathEnds (S.cellType c).1).isSome)
    (hs : S.walk ((S.pathEnds (S.cellType c).1).get hc).1 (S.cellType c).1 =
      some ((S.pathEnds (S.cellType c).1).get hc).2)
    (ht : S.walk ((S.pathEnds (S.cellType c).1).get hc).1 (S.cellType c).2 =
      some ((S.pathEnds (S.cellType c).1).get hc).2) :
    (I.toRoundBicat hS).cellReading c hc hs ht ≍
      𝟙 _ ◁ I.pathCls (Option.some_get hc).symm
        ((S.pathEnds_cellType_snd hS c).trans (Option.some_get hc).symm)
        (I.hasRoundType_cellDiagram hS x
          (Option.isSome_iff_exists.2 ⟨_, (Option.some_get hc).symm⟩)) := by
  cases c with
  | gen g =>
    exact (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans HEq.rfl)
  | unit p =>
    obtain _ | ⟨e, p'⟩ := p
    · exact absurd hc (by simp [pathEnds, cellType])
    have hcls := I.pathCls_unit (Option.some_get hc).symm
      (I.hasRoundType_cellDiagram hS x (Option.isSome_iff_exists.2 ⟨_, (Option.some_get hc).symm⟩))
    exact (congr_arg_heq (𝟙 ·) (I.pathComp_toPath hs (Option.some_get hc).symm)).trans
      (heq_of_eq ((congrArg (𝟙 _ ◁ ·) hcls).trans (whiskerLeft_id _ _)).symm)
  | unitor k e => exact I.unitorReading_toRoundBicat_heq hS k e hs ht _ _ _

variable [DecidableEq S.Ed]

theorem layerReading_toRoundBicat_heq (c : Cell S.Pt S.Ed S.Ce) (o : ℕ)
    {p p' : List (Edge S.Pt S.Ed)} (hl : S.applyLayer p c o = some p') {x y : S.Pt}
    (hp : S.walk x p = some y) (hp' : S.walk x p' = some y) (hpe : S.pathEnds p = some (x, y))
    (hpe' : S.pathEnds p' = some (x, y)) (hne : p ≠ [])
    (hy : HasRoundType (I.diagram ⟨p, [(c, o)]⟩ hne) (I.pathRound p (S.isPath_of_pathEnds hpe))
      (I.pathRound p' (S.isPath_of_pathEnds hpe'))) :
    (I.toRoundBicat hS).layerReading c o hl hp hp' ≍ 𝟙 _ ◁ I.pathCls hpe hpe' hy := by
  have hw := S.walk_of_applyLayer hl hp
  have hc := S.isSome_pathEnds_of_applyLayer hl hp
  obtain ⟨hne', hseg, hp'eq⟩ := S.eq_of_applyLayer_eq_some hl
  have hlen : (p.take o).length = o := by
    have h := congrArg List.length hseg
    simp only [List.length_append, List.length_take, List.length_drop] at h
    have := List.length_pos_iff.2 hne'
    simp only [List.length_take]
    omega
  have hcr := I.cellReading_toRoundBicat_heq hS (I.path p hne).unit c hc hw.2.1
    (S.walk_cellType_snd hS hc)
  have key := I.pathWhisker_heq hw.1 hw.2.1 (S.walk_cellType_snd hS hc) (Option.some_get hc).symm
    ((S.pathEnds_cellType_snd hS c).trans (Option.some_get hc).symm) hw.2.2 _ hcr
  refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans (key.trans
    (whiskerLeft_heq rfl (I.pathHom_congr ?_ _ _) (I.pathHom_congr ?_ _ _)
      (I.pathCls_heq ?_ ?_ ?_ _ _))))
  · exact (List.append_assoc _ _ _).symm.trans hseg
  · exact (List.append_assoc _ _ _).symm.trans hp'eq.symm
  · exact (List.append_assoc _ _ _).symm.trans hseg
  · exact (List.append_assoc _ _ _).symm.trans hp'eq.symm
  · exact PastingDiagram.equiv_of_eq
      (I.diagram_singleton (l := (c, o)) hne hseg.symm hlen hne' (I.path p hne).unit).symm

theorem evalFrom_toRoundBicat_heq : ∀ (ls : List (Cell S.Pt S.Ed S.Ce × ℕ))
    (p : List (Edge S.Pt S.Ed)) {x y : S.Pt} (hp : S.walk x p = some y)
    {q : List (Edge S.Pt S.Ed)} (h : S.targetFrom p ls = some q) (hq : S.walk x q = some y)
    (hpe : S.pathEnds p = some (x, y)) (hqe : S.pathEnds q = some (x, y))
    (hd : S.target ⟨p, ls⟩ = some q),
    (I.toRoundBicat hS).evalFrom ls p hp h hq ≍
      𝟙 _ ◁ I.pathCls hpe hqe (I.hasRoundType_diagram hS hd (S.isPath_of_pathEnds hpe).ne_nil)
  | [], p, x, y, hp, q, h, hq, hpe, hqe, hd => by
    obtain rfl : p = q := Option.some.inj h
    refine (heq_of_eq (eqToHom_refl _ _)).trans
      ((congr_arg_heq (𝟙 ·) (I.pathComp_toPath hp hpe)).trans (heq_of_eq ?_))
    exact (Bicategory.whiskerLeft_id _ _).symm.trans (congrArg _ (I.pathCls_eq_id hpe
      (PastingDiagram.equiv_of_eq (I.diagram_nil _)) _).symm)
  | l :: ls, p, x, y, hp, q, h, hq, hpe, hqe, hd => by
    obtain ⟨h₁, h₂⟩ := S.targetFrom_cons_eq_some h
    have hpe' := S.pathEnds_applyLayer hS h₁ hpe
    have hpath := S.isPath_of_pathEnds hpe
    have hd₁ : S.target ⟨p, [l]⟩ = some (S.rewrite p l) := S.target_singleton hpath h₁
    have hd₂ : S.target ⟨S.rewrite p l, ls⟩ = some q := by
      rw [target, if_pos (S.isPath_of_pathEnds hpe')]
      exact h₂
    have hL := I.layerReading_toRoundBicat_heq hS l.1 l.2 h₁ hp (S.walk_applyLayer hS h₁ hp) hpe
      hpe' hpath.ne_nil (I.hasRoundType_diagram hS hd₁ hpath.ne_nil)
    have hR := evalFrom_toRoundBicat_heq ls (S.rewrite p l) (S.walk_applyLayer hS h₁ hp) h₂ hq
      hpe' hqe hd₂
    refine (heq_comp (I.pathComp_toPath _ hpe) (I.pathComp_toPath _ hpe')
      (I.pathComp_toPath _ hqe) hL hR).trans (heq_of_eq ?_)
    refine (Bicategory.whiskerLeft_comp _ _ _).symm.trans (congrArg _ ?_)
    obtain _ | ⟨l', ls'⟩ := ls
    · obtain rfl : S.rewrite p l = q := Option.some.inj h₂
      exact (congrArg _ (I.pathCls_eq_id hpe' (PastingDiagram.equiv_of_eq (I.diagram_nil _))
        _)).trans (Category.comp_id _)
    · obtain ⟨hpst, e⟩ := I.equiv_diagram_append hS (d := ⟨p, [l]⟩)
        (d' := ⟨S.rewrite p l, l' :: ls'⟩) hd₁ rfl hpath.ne_nil
        (S.isPath_of_pathEnds hpe').ne_nil (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
        (by rw [hd₂]; rfl)
      exact I.pathCls_comp hpe hpe' hqe _ _ _ hpst e

noncomputable def roundCell (d : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) :
    RoundBicat.Cell (I.pathHom hx) (I.pathHom (S.pathEnds_target hS hq hx)) :=
  I.pathCell hx (S.pathEnds_target hS hq hx)
    (I.hasRoundType_roundDiagram hS hq (S.isPath_of_pathEnds hx).ne_nil)
    (I.roundDiagram hS hq (S.isPath_of_pathEnds hx).ne_nil).isRound rfl rfl

theorem pathCls_diagram (d : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) :
    I.pathCls hx (S.pathEnds_target hS hq hx)
        (I.hasRoundType_diagram hS hq (S.isPath_of_pathEnds hx).ne_nil) =
      RoundBicat.homMk (I.roundCell hS d hx hq) := by
  have hsrc := (S.isPath_of_pathEnds hx).ne_nil
  obtain ⟨p, _ | ⟨l, ls⟩⟩ := d
  · obtain rfl : p = q := Option.some.inj (S.targetFrom_of_target hq)
    exact (I.pathCls_eq_id hx (PastingDiagram.equiv_of_eq (I.diagram_nil _)) _).trans
      ((I.pathCls_eq_id hx (PastingDiagram.equiv_of_eq (I.diagram_unit_singleton hsrc))
        (I.hasRoundType_roundDiagram hS hq hsrc)).symm.trans (I.pathCls_eq_homMk _ _ _ _ rfl))
  · obtain ⟨hp, e⟩ := I.exists_equiv_roundDiagram hS hq hsrc (List.cons_ne_nil _ _)
    have hy := I.hasRoundType_diagram hS hq hsrc
    have hb := (hy.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hx)) false).unit
    exact RoundBicat.homMk_rounding_eq_homMk_unitFirst (n := 0)
      (hy.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hx))))
      (hp.of_equiv hb.symm (.refl _)) _ (I.roundCell hS _ hx hq) (.refl _)
      (e.trans (Equiv.paste hb.symm (.refl _) hp _))

theorem evalB_toRoundBicat (d : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) :
    (I.toRoundBicat hS).evalB d hx hq =
      eqToHom (I.pathComp_toPath _ hx) ≫ 𝟙 _ ◁ RoundBicat.homMk (I.roundCell hS d hx hq) ≫
        eqToHom (I.pathComp_toPath _ (S.pathEnds_target hS hq hx)).symm := by
  refine (conj_eqToHom_iff_heq _ _ _ (I.pathComp_toPath _ (S.pathEnds_target hS hq hx))).2
    ((I.evalFrom_toRoundBicat_heq hS d.layers d.source _
    (S.targetFrom_of_target hq) _ hx (S.pathEnds_target hS hq hx) hq).trans ?_)
  exact heq_of_eq (congrArg _ (I.pathCls_diagram hS d hx hq))

theorem equivalent_roundDiagram_unitApply (m : UnitMove) {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.unitApply m d h = some d') {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hq' : S.target d' = some q') (hsrc' : d'.source ≠ []) :
    Equivalent (I.roundDiagram hS hq hsrc) (I.roundDiagram hS hq' hsrc') := by
  obtain rfl : q = q' :=
    Option.some.inj (hq.symm.trans ((S.target_unitApply hS hd).symm.trans hq'))
  obtain ⟨x, y, hx⟩ := S.exists_pathEnds_of_isPath (S.isPath_source_of_target hq)
  have hx' := S.pathEnds_source_unitApply hd hx
  have e := (I.evalB_toRoundBicat hS d hx hq).symm.trans
    (((I.toRoundBicat hS).evalB_eq_of_unitApply m hd hx hq).trans
      (congrArg _ (I.evalB_toRoundBicat hS d' hx' hq')))
  have h₁ := ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans ((heq_of_eq e).trans
    ((eqToHom_comp_heq _ _).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))))
  exact RoundBicat.equivalent_of_homMk_heq _ _ (I.pathHom_congr (S.source_unitApply hd).symm _ _)
    rfl (heq_of_id_whiskerLeft_heq (I.pathHom_congr (S.source_unitApply hd).symm _ _) rfl h₁)

end Signature.Interp

end Layered

end Atoms.Diagrammatic
