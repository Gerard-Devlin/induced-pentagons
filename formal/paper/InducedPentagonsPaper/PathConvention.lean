import InducedPentagonsPaper.ProfileData

/-! Relating ordered path tuples to the usual induced-subgraph isomorphism
definition of a four-vertex path. -/

namespace InducedPentagons.Paper

def pathAdj (i j : Fin 4) : Bool := i.val + 1 == j.val || j.val + 1 == i.val

def pathGraph : Graph (Fin 4) where
  adj := pathAdj
  symmetric := by decide +kernel
  loopless := by decide +kernel

def PathTuple.vertex {n : Nat} (p : PathTuple n) (i : Fin 4) : Fin n :=
  match i.val with
  | 0 => p.a
  | 1 => p.b
  | 2 => p.c
  | _ => p.d

def PathTuple.reverse {n : Nat} (p : PathTuple n) : PathTuple n := ⟨p.d, p.c, p.b, p.a⟩

def pathVertices {n : Nat} (p : PathTuple n) : Finset (Fin n) :=
  Finset.univ.image p.vertex

theorem path_has_no_twins : ∀ i j : Fin 4,
    (∀ k : Fin 4, pathAdj i k = pathAdj j k) → i = j := by decide +kernel

def pathReverseIndex (i : Fin 4) : Fin 4 := ⟨3 - i.val, by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem path_self_maps : ∀ f : Fin 4 → Fin 4,
    (∀ i j, pathAdj (f i) (f j) = pathAdj i j) →
      (∀ i, f i = i) ∨ (∀ i, f i = pathReverseIndex i) := by decide +kernel

theorem pathTuple_pattern {n : Nat} {g : Graph (Fin n)} {p : PathTuple n}
    (h : IsInducedPath g p) : ∀ i j, g.adj (p.vertex i) (p.vertex j) = pathAdj i j := by
  rcases h with ⟨_, hab, hbc, hcd, hac, had, hbd⟩
  have hba : g.adj p.b p.a = true := (g.symmetric p.b p.a).trans hab
  have hcb : g.adj p.c p.b = true := (g.symmetric p.c p.b).trans hbc
  have hdc : g.adj p.d p.c = true := (g.symmetric p.d p.c).trans hcd
  have hca : g.adj p.c p.a = false := (g.symmetric p.c p.a).trans hac
  have hda : g.adj p.d p.a = false := (g.symmetric p.d p.a).trans had
  have hdb : g.adj p.d p.b = false := (g.symmetric p.d p.b).trans hbd
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PathTuple.vertex, pathAdj, g.loopless, hab, hbc, hcd, hac, had, hbd,
      hba, hcb, hdc, hca, hda, hdb]

theorem pathTuple_vertex_injective {n : Nat} {g : Graph (Fin n)} {p : PathTuple n}
    (h : IsInducedPath g p) : Function.Injective p.vertex := by
  intro i j hij
  apply path_has_no_twins i j
  intro k
  rw [← pathTuple_pattern h i k, ← pathTuple_pattern h j k, hij]

theorem pathVertices_card {n : Nat} {g : Graph (Fin n)} {p : PathTuple n}
    (h : IsInducedPath g p) : (pathVertices p).card = 4 := by
  rw [pathVertices, Finset.card_image_of_injective _ (pathTuple_vertex_injective h)]
  simp

theorem reverse_isInducedPath {n : Nat} {g : Graph (Fin n)} {p : PathTuple n}
    (h : IsInducedPath g p) : IsInducedPath g p.reverse := by
  rcases h with ⟨hn, hab, hbc, hcd, hac, had, hbd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [PathTuple.reverse, ne_comm] using hn.reverse
  · exact (g.symmetric p.d p.c).trans hcd
  · exact (g.symmetric p.c p.b).trans hbc
  · exact (g.symmetric p.b p.a).trans hab
  · exact (g.symmetric p.d p.b).trans hbd
  · exact (g.symmetric p.d p.a).trans had
  · exact (g.symmetric p.c p.a).trans hac

theorem pathVertices_reverse {n : Nat} (p : PathTuple n) :
    pathVertices p.reverse = pathVertices p := by
  have h : ∀ i : Fin 4, p.reverse.vertex i = p.vertex (pathReverseIndex i) := by
    intro i
    fin_cases i <;> rfl
  have hsurj : Function.Surjective pathReverseIndex := by decide +kernel
  apply Finset.ext
  intro v
  simp only [pathVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨pathReverseIndex i, (h i).symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hsurj i
    exact ⟨j, (h j).trans (congrArg p.vertex hj)⟩

def InducedPathSet {n : Nat} (g : Graph (Fin n)) (s : Finset (Fin n)) : Prop :=
  Nonempty ((toSimpleGraph pathGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n)))

noncomputable def pathTupleIso {n : Nat} {g : Graph (Fin n)} {p : PathTuple n}
    (h : IsInducedPath g p) :
    (toSimpleGraph pathGraph) ≃g (toSimpleGraph g).induce (pathVertices p : Set (Fin n)) where
  toEquiv := Equiv.ofBijective (fun i => ⟨p.vertex i, by simp [pathVertices]⟩) (by
    constructor
    · intro i j hij
      exact pathTuple_vertex_injective h (congrArg Subtype.val hij)
    · intro v
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp v.property
      exact ⟨i, Subtype.ext hi⟩)
  map_rel_iff' := by
    intro i j
    change g.adj (p.vertex i) (p.vertex j) = true ↔ pathAdj i j = true
    rw [pathTuple_pattern h]

theorem pathTuple_inducedPathSet {n : Nat} {g : Graph (Fin n)} {p : PathTuple n}
    (h : IsInducedPath g p) : InducedPathSet g (pathVertices p) := ⟨pathTupleIso h⟩

noncomputable def tupleOfPathIso {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph pathGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n))) : PathTuple n :=
  ⟨(e 0).val, (e 1).val, (e 2).val, (e 3).val⟩

theorem tupleOfPathIso_vertex {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph pathGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n)))
    (i : Fin 4) : (tupleOfPathIso e).vertex i = (e i).val := by
  fin_cases i <;> rfl

theorem tupleOfPathIso_induced {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph pathGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n))) :
    IsInducedPath g (tupleOfPathIso e) := by
  have hinj : Function.Injective (fun i : Fin 4 => (e i).val) := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hn := (List.nodup_finRange 4).map hinj
  have hpat : ∀ i j : Fin 4, g.adj (e i).val (e j).val = pathAdj i j := by
    intro i j
    have h : g.adj (e i).val (e j).val = true ↔ pathAdj i j = true := e.map_rel_iff
    cases hg : g.adj (e i).val (e j).val <;> cases hp : pathAdj i j <;> simp_all
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [tupleOfPathIso, pathAdj] using hpat 0 1
  · simpa [tupleOfPathIso, pathAdj] using hpat 1 2
  · simpa [tupleOfPathIso, pathAdj] using hpat 2 3
  · simpa [tupleOfPathIso, pathAdj] using hpat 0 2
  · simpa [tupleOfPathIso, pathAdj] using hpat 0 3
  · simpa [tupleOfPathIso, pathAdj] using hpat 1 3

theorem tupleOfPathIso_vertices {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph pathGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n))) :
    pathVertices (tupleOfPathIso e) = s := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    rw [tupleOfPathIso_vertex] at hi
    exact hi ▸ (e i).property
  · intro hv
    obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ _, (tupleOfPathIso_vertex e i).trans (congrArg Subtype.val hi)⟩

theorem inducedPathSet_iff_exists_tuple {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)} :
    InducedPathSet g s ↔ ∃ p, IsInducedPath g p ∧ pathVertices p = s := by
  constructor
  · rintro ⟨e⟩
    exact ⟨tupleOfPathIso e, tupleOfPathIso_induced e, tupleOfPathIso_vertices e⟩
  · rintro ⟨p, hp, rfl⟩
    exact pathTuple_inducedPathSet hp

theorem inducedPathSet_iff_mem_inducedPaths {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)} :
    InducedPathSet g s ↔ ∃ p ∈ inducedPaths g, pathVertices p = s := by
  constructor
  · intro hs
    obtain ⟨p, hp, hvs⟩ := inducedPathSet_iff_exists_tuple.mp hs
    have hne : p.a ≠ p.d := by
      intro he
      have ha := (List.nodup_cons.mp hp.1).1
      exact ha (by simp [he])
    by_cases hlt : p.a < p.d
    · exact ⟨p, (mem_inducedPaths g p).mpr ⟨hlt, hp⟩, hvs⟩
    · have hrev : p.d < p.a := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      exact ⟨p.reverse, (mem_inducedPaths g p.reverse).mpr ⟨hrev, reverse_isInducedPath hp⟩,
        (pathVertices_reverse p).trans hvs⟩
  · rintro ⟨p, hp, rfl⟩
    exact pathTuple_inducedPathSet ((mem_inducedPaths g p).mp hp).2

noncomputable def pathTupleIsoOn {n : Nat} {g : Graph (Fin n)} {p : PathTuple n}
    (h : IsInducedPath g p) (s : Finset (Fin n)) (hs : pathVertices p = s) :
    (toSimpleGraph pathGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n)) where
  toEquiv := Equiv.ofBijective (fun i => ⟨p.vertex i, by rw [← hs]; simp [pathVertices]⟩) (by
    constructor
    · intro i j hij
      exact pathTuple_vertex_injective h (congrArg Subtype.val hij)
    · intro v
      have hv : v.val ∈ pathVertices p := by rw [hs]; exact v.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      exact ⟨i, Subtype.ext hi⟩)
  map_rel_iff' := by
    intro i j
    change g.adj (p.vertex i) (p.vertex j) = true ↔ pathAdj i j = true
    rw [pathTuple_pattern h]

theorem pathTuple_ext {n : Nat} (p q : PathTuple n) (h : ∀ i, p.vertex i = q.vertex i) : p = q := by
  cases p with
  | mk a b c d =>
    cases q with
    | mk w x y z =>
      have ha : a = w := h 0
      have hb : b = x := h 1
      have hc : c = y := h 2
      have hd : d = z := h 3
      cases ha; cases hb; cases hc; cases hd
      rfl

theorem normalized_path_unique {n : Nat} {g : Graph (Fin n)} {p q : PathTuple n}
    (hp : IsInducedPath g p) (hq : IsInducedPath g q) (hp' : p.a < p.d) (hq' : q.a < q.d)
    (hvs : pathVertices p = pathVertices q) : p = q := by
  let ep := pathTupleIsoOn hp (pathVertices p) rfl
  let eq := pathTupleIsoOn hq (pathVertices p) hvs.symm
  let e := ep.trans eq.symm
  have hpoint : ∀ i, q.vertex (e i) = p.vertex i := by
    intro i
    exact congrArg Subtype.val (eq.apply_symm_apply (ep i))
  have hrel : ∀ i j, pathAdj (e i) (e j) = pathAdj i j := by
    intro i j
    have h : pathAdj (e i) (e j) = true ↔ pathAdj i j = true := e.map_rel_iff
    cases h1 : pathAdj (e i) (e j) <;> cases h2 : pathAdj i j <;> simp_all
  rcases path_self_maps (fun i => e i) hrel with hid | hrev
  · apply pathTuple_ext p q
    intro i
    have h := hpoint i
    rw [hid i] at h
    exact h.symm
  · have h0 := hpoint 0
    have h3 := hpoint 3
    rw [hrev 0] at h0
    rw [hrev 3] at h3
    change q.d = p.a at h0
    change q.a = p.d at h3
    have hback : q.d < q.a := by rw [h0, h3]; exact hp'
    exact False.elim ((lt_asymm hq') hback)

theorem inducedPaths_vertices_injective {n : Nat} (g : Graph (Fin n))
    {p q : PathTuple n} (hp : p ∈ inducedPaths g) (hq : q ∈ inducedPaths g)
    (hvs : pathVertices p = pathVertices q) : p = q := by
  have hp' := (mem_inducedPaths g p).mp hp
  have hq' := (mem_inducedPaths g q).mp hq
  exact normalized_path_unique hp'.2 hq'.2 hp'.1 hq'.1 hvs

noncomputable def pathSubsetEquiv {n : Nat} (g : Graph (Fin n)) :
    ↥(inducedPaths g).toFinset ≃ {s : Finset (Fin n) // InducedPathSet g s} :=
  Equiv.ofBijective (fun p => ⟨pathVertices p.val,
    pathTuple_inducedPathSet ((mem_inducedPaths g p.val).mp (List.mem_toFinset.mp p.property)).2⟩) (by
    constructor
    · intro p q hpq
      apply Subtype.ext
      exact inducedPaths_vertices_injective g (List.mem_toFinset.mp p.property)
        (List.mem_toFinset.mp q.property) (congrArg Subtype.val hpq)
    · intro s
      obtain ⟨p, hp, he⟩ := inducedPathSet_iff_mem_inducedPaths.mp s.property
      exact ⟨⟨p, List.mem_toFinset.mpr hp⟩, Subtype.ext he⟩)

theorem pathVertices_eq_list {n : Nat} (p : PathTuple n) :
    pathVertices p = {p.a, p.b, p.c, p.d} := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    fin_cases i <;> simp [PathTuple.vertex]
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h
    · subst v; exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · subst v; exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    · subst v; exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
    · subst v; exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩

def pathSetLiteral {n : Nat} (g : Graph (Fin n)) (s : Finset (Fin n)) (v : Fin n) : Option Bool :=
  if v ∈ s then
    if (s.filter (fun w => g.adj v w)).card = 1 then some true else some false
  else none

theorem pathSetLiteral_eq {n : Nat} {g : Graph (Fin n)} {p : PathTuple n}
    (hp : IsInducedPath g p) : pathSetLiteral g (pathVertices p) = pathLiteral p := by
  have hn := hp.1
  simp at hn
  rcases hn with ⟨⟨hneab, hneac, hnead⟩, ⟨hnebc, hnebd⟩, hnecd⟩
  rcases hp with ⟨_, hab, hbc, hcd, hac, had, hbd⟩
  have hba : g.adj p.b p.a = true := (g.symmetric p.b p.a).trans hab
  have hcb : g.adj p.c p.b = true := (g.symmetric p.c p.b).trans hbc
  have hdc : g.adj p.d p.c = true := (g.symmetric p.d p.c).trans hcd
  have hca : g.adj p.c p.a = false := (g.symmetric p.c p.a).trans hac
  have hda : g.adj p.d p.a = false := (g.symmetric p.d p.a).trans had
  have hdb : g.adj p.d p.b = false := (g.symmetric p.d p.b).trans hbd
  funext v
  by_cases hv : v ∈ pathVertices p
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    fin_cases i <;>
      simp_all [pathSetLiteral, pathVertices_eq_list, PathTuple.vertex, pathLiteral, g.loopless,
        Finset.filter_insert, Finset.filter_singleton, ne_comm]
  · have ha : v ≠ p.a := by intro h; apply hv; rw [pathVertices_eq_list, h]; simp
    have hb : v ≠ p.b := by intro h; apply hv; rw [pathVertices_eq_list, h]; simp
    have hc : v ≠ p.c := by intro h; apply hv; rw [pathVertices_eq_list, h]; simp
    have hd : v ≠ p.d := by intro h; apply hv; rw [pathVertices_eq_list, h]; simp
    simp [pathSetLiteral, hv, pathLiteral, ha, hb, hc, hd]

noncomputable def setProfileLink {n : Nat} (g : Graph (Fin n)) (x : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ s : {s : Finset (Fin n) // InducedPathSet g s}, patternValue (pathSetLiteral g s.val) x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem profileLink_eq_setProfileLink (x : Fin 16 → ℝ) :
    profileLink x = setProfileLink clebsch x := by
  classical
  have h := Fintype.sum_equiv (pathSubsetEquiv clebsch)
    (fun p => patternValue (pathLiteral p.val) x)
    (fun s => patternValue (pathSetLiteral clebsch s.val) x) (by
      intro p
      change patternValue (pathLiteral p.val) x = patternValue (pathSetLiteral clebsch (pathVertices p.val)) x
      rw [pathSetLiteral_eq ((mem_inducedPaths clebsch p.val).mp (List.mem_toFinset.mp p.property)).2])
  have hl : (∑ p : ↥(inducedPaths clebsch).toFinset, patternValue (pathLiteral p.val) x) =
      ∑ p ∈ (inducedPaths clebsch).toFinset, patternValue (pathLiteral p) x :=
    Finset.sum_coe_sort ((inducedPaths clebsch).toFinset) (fun p => patternValue (pathLiteral p) x)
  unfold profileLink setProfileLink
  rw [← List.sum_toFinset _ (inducedPaths_nodup clebsch)]
  exact hl.symm.trans h

end InducedPentagons.Paper
