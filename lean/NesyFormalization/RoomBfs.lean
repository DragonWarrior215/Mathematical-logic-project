import NesyFormalization.HighPlanner

namespace EnvFormalization

abbrev RoomCoord := Int × Int

structure RoomGraph where
  edge : RoomCoord → Direction → RoomCoord → Prop

abbrev RoomHop := Direction × RoomCoord

def ValidRoomHops (g : RoomGraph) : RoomCoord → List RoomHop → Prop
  | _, [] => True
  | current, (dir, next) :: rest =>
      g.edge current dir next ∧ ValidRoomHops g next rest

def routeEnd : RoomCoord → List RoomHop → RoomCoord
  | current, [] => current
  | _, (_, next) :: rest => routeEnd next rest

structure RoomRoute (g : RoomGraph) (start target : RoomCoord) where
  hops : List RoomHop
  valid : ValidRoomHops g start hops
  endsAt : routeEnd start hops = target

def RoomReachable (g : RoomGraph) (start target : RoomCoord) : Prop :=
  Nonempty (RoomRoute g start target)

def RouteAvoidsLocked
    (g : RoomGraph) (locked : RoomGraph → RoomCoord → Direction → Prop) :
    RoomCoord → List RoomHop → Prop
  | _, [] => True
  | current, (dir, next) :: rest =>
      ¬ locked g current dir ∧ RouteAvoidsLocked g locked next rest

def RouteShortest (g : RoomGraph) {start target : RoomCoord}
    (route : RoomRoute g start target) : Prop :=
  ∀ other : RoomRoute g start target, route.hops.length ≤ other.hops.length

def firstHopOfRoute {g : RoomGraph} {start target : RoomCoord}
    (route : RoomRoute g start target) : Option Direction :=
  route.hops.head?.map Prod.fst

theorem first_hop_sound {g : RoomGraph} {start target : RoomCoord}
    (route : RoomRoute g start target) {dir : Direction}
    (hhop : firstHopOfRoute route = some dir) :
    ∃ next, g.edge start dir next := by
  cases h : route.hops with
  | nil => simp [firstHopOfRoute, h] at hhop
  | cons hop rest =>
      rcases hop with ⟨d, next⟩
      simp [firstHopOfRoute, h] at hhop
      subst d
      have hv : g.edge start dir next ∧ ValidRoomHops g next rest := by
        simpa [h, ValidRoomHops] using route.valid
      exact ⟨next, hv.1⟩

theorem first_hop_respects_locked_exit
    {g : RoomGraph} {start target : RoomCoord}
    (locked : RoomGraph → RoomCoord → Direction → Prop)
    (route : RoomRoute g start target)
    (havoid : RouteAvoidsLocked g locked start route.hops)
    {dir : Direction} (hhop : firstHopOfRoute route = some dir) :
    ¬ locked g start dir := by
  cases h : route.hops with
  | nil => simp [firstHopOfRoute, h] at hhop
  | cons hop rest =>
      rcases hop with ⟨d, next⟩
      simp [firstHopOfRoute, h] at hhop
      subst d
      have hv : ¬ locked g start dir ∧ RouteAvoidsLocked g locked next rest := by
        simpa [h, RouteAvoidsLocked] using havoid
      exact hv.1

theorem route_shortest_length_bound {g : RoomGraph} {start target : RoomCoord}
    (route : RoomRoute g start target) (hshort : RouteShortest g route) :
    ∀ other : RoomRoute g start target,
      route.hops.length ≤ other.hops.length := hshort

theorem first_hop_complete_of_route {g : RoomGraph} {start target : RoomCoord}
    (route : RoomRoute g start target) (hne : start ≠ target) :
    ∃ dir, firstHopOfRoute route = some dir := by
  cases h : route.hops with
  | nil =>
      exfalso
      apply hne
      simpa [h, routeEnd] using route.endsAt
  | cons hop rest =>
      rcases hop with ⟨dir, next⟩
      exact ⟨dir, by simp [firstHopOfRoute, h]⟩

theorem first_hop_none_unreachable_of_complete
    (choose : ∀ {g : RoomGraph} {start target : RoomCoord},
      RoomReachable g start target → start ≠ target →
      ∃ route : RoomRoute g start target, firstHopOfRoute route ≠ none)
    {g : RoomGraph} {start target : RoomCoord}
    (hallNone : ∀ route : RoomRoute g start target,
      firstHopOfRoute route = none) (hne : start ≠ target) :
    ¬ RoomReachable g start target := by
  intro reachable
  obtain ⟨route, hsome⟩ := choose reachable hne
  exact hsome (hallNone route)

/-! ## Graph-generic shortest route

These results do not require concrete rooms or a finite map.  Once any finite
route exists, well-ordering of `Nat` supplies one with minimum hop count. -/

theorem shortest_room_route_exists
    {g : RoomGraph} {start target : RoomCoord}
    (hreach : RoomReachable g start target) :
    ∃ route : RoomRoute g start target, RouteShortest g route := by
  rcases hreach with ⟨initial⟩
  have aux : ∀ n, ∀ route : RoomRoute g start target,
      route.hops.length = n →
      ∃ best : RoomRoute g start target, RouteShortest g best := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro route hlen
        by_cases hshorter : ∃ other : RoomRoute g start target,
            other.hops.length < n
        · obtain ⟨other, hother⟩ := hshorter
          exact ih other.hops.length hother other rfl
        · refine ⟨route, ?_⟩
          intro other
          rw [hlen]
          exact Nat.le_of_not_gt (fun h => hshorter ⟨other, h⟩)
  exact aux initial.hops.length initial rfl

noncomputable def shortestRoomRoute
    {g : RoomGraph} {start target : RoomCoord}
    (hreach : RoomReachable g start target) : RoomRoute g start target :=
  Classical.choose (shortest_room_route_exists hreach)

theorem shortestRoomRoute_shortest
    {g : RoomGraph} {start target : RoomCoord}
    (hreach : RoomReachable g start target) :
    RouteShortest g (shortestRoomRoute hreach) :=
  Classical.choose_spec (shortest_room_route_exists hreach)

/-- A specification-level first-hop planner.  It is deliberately
noncomputable: its purpose is to close the mathematical specification without
assuming a concrete map; the FIFO implementation is verified separately. -/
noncomputable def verifiedFirstHop
    (g : RoomGraph) (start target : RoomCoord) : Option Direction := by
  classical
  exact if h : RoomReachable g start target then
    firstHopOfRoute (shortestRoomRoute h)
  else none

theorem verified_first_hop_shortest
    {g : RoomGraph} {start target : RoomCoord}
    (hreach : RoomReachable g start target) :
    ∀ other : RoomRoute g start target,
      (shortestRoomRoute hreach).hops.length ≤ other.hops.length := by
  exact shortestRoomRoute_shortest hreach

theorem verified_first_hop_complete
    {g : RoomGraph} {start target : RoomCoord}
    (hne : start ≠ target) (hreach : RoomReachable g start target) :
    ∃ dir, verifiedFirstHop g start target = some dir := by
  obtain ⟨dir, hdir⟩ := first_hop_complete_of_route
    (shortestRoomRoute hreach) hne
  refine ⟨dir, ?_⟩
  simp [verifiedFirstHop, hreach, hdir]

theorem verified_first_hop_none_unreachable
    {g : RoomGraph} {start target : RoomCoord}
    (hne : start ≠ target)
    (hnone : verifiedFirstHop g start target = none) :
    ¬ RoomReachable g start target := by
  intro hreach
  obtain ⟨dir, hdir⟩ := verified_first_hop_complete hne hreach
  rw [hnone] at hdir
  contradiction

/-! The three closed, graph-generic specifications from the theorem list. -/

theorem first_hop_shortest
    {g : RoomGraph} {start target : RoomCoord}
    (hreach : RoomReachable g start target) :
    ∀ other : RoomRoute g start target,
      (shortestRoomRoute hreach).hops.length ≤ other.hops.length :=
  verified_first_hop_shortest hreach

theorem first_hop_complete
    {g : RoomGraph} {start target : RoomCoord}
    (hne : start ≠ target) (hreach : RoomReachable g start target) :
    ∃ dir, verifiedFirstHop g start target = some dir :=
  verified_first_hop_complete hne hreach

theorem first_hop_none_unreachable
    {g : RoomGraph} {start target : RoomCoord}
    (hne : start ≠ target)
    (hnone : verifiedFirstHop g start target = none) :
    ¬ RoomReachable g start target :=
  verified_first_hop_none_unreachable hne hnone

/-! ## Executable certified room BFS

`RoomGraph.edge` is a proposition, so an executable search additionally needs
an enumeration of outgoing edges.  Each enumerated neighbor carries a proof
that it is a real graph edge. -/

structure CertifiedNeighbor (g : RoomGraph) (room : RoomCoord) where
  dir : Direction
  next : RoomCoord
  edge_ok : g.edge room dir next

structure FiniteRoomGraph extends RoomGraph where
  rooms : List RoomCoord
  rooms_nodup : rooms.Nodup
  neighbors : (room : RoomCoord) → List (CertifiedNeighbor toRoomGraph room)
  /-- Every propositional edge is visible to the executable search.  Together
  with `CertifiedNeighbor.edge_ok`, this makes `edge` and `neighbors` agree in
  both directions. -/
  neighbors_complete : ∀ room dir next,
    toRoomGraph.edge room dir next →
    ∃ neighbor ∈ neighbors room,
      neighbor.dir = dir ∧ neighbor.next = next
  edge_rooms : ∀ room dir next,
    toRoomGraph.edge room dir next → room ∈ rooms ∧ next ∈ rooms

theorem finiteRoomGraph_edge_iff_neighbor
    (g : FiniteRoomGraph) (room : RoomCoord) (dir : Direction)
    (next : RoomCoord) :
    g.edge room dir next ↔
      ∃ neighbor ∈ g.neighbors room,
        neighbor.dir = dir ∧ neighbor.next = next := by
  constructor
  · exact g.neighbors_complete room dir next
  · rintro ⟨neighbor, _, hdir, hnext⟩
    simpa [hdir, hnext] using neighbor.edge_ok

theorem finiteRoomGraph_neighbor_in_rooms
    (g : FiniteRoomGraph) (room : RoomCoord)
    (neighbor : CertifiedNeighbor g.toRoomGraph room) :
    room ∈ g.rooms ∧ neighbor.next ∈ g.rooms :=
  g.edge_rooms room neighbor.dir neighbor.next neighbor.edge_ok

/-! ## Agent routing context and executable lock filtering -/

structure RoomRoutingContext where
  keys : Nat
  visitedExit : RoomCoord → Direction → Bool
  locked : RoomCoord → Direction → Bool

/-- This is the Lean counterpart of Python's condition
`not (exit_state == "locked" and direction not in visited_exits and keys == 0)`. -/
def roomEdgeAllowed (ctx : RoomRoutingContext)
    (room : RoomCoord) (dir : Direction) : Bool :=
  !ctx.locked room dir || ctx.keys > 0 || ctx.visitedExit room dir

theorem roomEdgeAllowed_locked_no_key_unvisited
    (ctx : RoomRoutingContext) (room : RoomCoord) (dir : Direction)
    (hlocked : ctx.locked room dir = true)
    (hkeys : ctx.keys = 0)
    (hunvisited : ctx.visitedExit room dir = false) :
    roomEdgeAllowed ctx room dir = false := by
  simp [roomEdgeAllowed, hlocked, hkeys, hunvisited]

theorem roomEdgeAllowed_of_key
    (ctx : RoomRoutingContext) (room : RoomCoord) (dir : Direction)
    (hkeys : 0 < ctx.keys) : roomEdgeAllowed ctx room dir = true := by
  simp [roomEdgeAllowed, hkeys]

theorem roomEdgeAllowed_of_visited
    (ctx : RoomRoutingContext) (room : RoomCoord) (dir : Direction)
    (hvisited : ctx.visitedExit room dir = true) :
    roomEdgeAllowed ctx room dir = true := by
  simp [roomEdgeAllowed, hvisited]

structure CertifiedAllowedNeighbor
    (g : RoomGraph) (ctx : RoomRoutingContext) (room : RoomCoord) where
  dir : Direction
  next : RoomCoord
  edge_ok : g.edge room dir next
  allowed : roomEdgeAllowed ctx room dir = true

/-- Only neighbors that the current inventory/visited-exit state permits. -/
def allowedRoomNeighbors (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (room : RoomCoord) :
    List (CertifiedAllowedNeighbor g.toRoomGraph ctx room) :=
  (g.neighbors room).filterMap fun neighbor =>
    if h : roomEdgeAllowed ctx room neighbor.dir = true then
      some {
        dir := neighbor.dir
        next := neighbor.next
        edge_ok := neighbor.edge_ok
        allowed := h
      }
    else none

theorem allowedRoomNeighbors_member
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (room : RoomCoord)
    (neighbor : CertifiedAllowedNeighbor g.toRoomGraph ctx room)
    (_hmem : neighbor ∈ allowedRoomNeighbors g ctx room) :
    g.edge room neighbor.dir neighbor.next ∧
      roomEdgeAllowed ctx room neighbor.dir = true :=
  ⟨neighbor.edge_ok, neighbor.allowed⟩

theorem allowedRoomNeighbors_complete
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (room : RoomCoord) (dir : Direction) (next : RoomCoord)
    (hedge : g.edge room dir next)
    (hallowed : roomEdgeAllowed ctx room dir = true) :
    ∃ neighbor ∈ allowedRoomNeighbors g ctx room,
      neighbor.dir = dir ∧ neighbor.next = next := by
  obtain ⟨base, hbase, hdir, hnext⟩ :=
    g.neighbors_complete room dir next hedge
  subst dir
  subst next
  let allowedNeighbor : CertifiedAllowedNeighbor g.toRoomGraph ctx room := {
    dir := base.dir
    next := base.next
    edge_ok := base.edge_ok
    allowed := hallowed
  }
  refine ⟨allowedNeighbor, ?_, rfl, rfl⟩
  unfold allowedRoomNeighbors
  rw [List.mem_filterMap]
  exact ⟨base, hbase, by simp [hallowed, allowedNeighbor]⟩

theorem locked_no_key_unvisited_not_allowed
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (room : RoomCoord) (dir : Direction)
    (hlocked : ctx.locked room dir = true)
    (hkeys : ctx.keys = 0)
    (hunvisited : ctx.visitedExit room dir = false) :
    ∀ neighbor ∈ allowedRoomNeighbors g ctx room,
      neighbor.dir ≠ dir := by
  intro neighbor hmem heq
  have hallowed := neighbor.allowed
  rw [heq] at hallowed
  rw [roomEdgeAllowed_locked_no_key_unvisited ctx room dir
    hlocked hkeys hunvisited] at hallowed
  contradiction

theorem validRoomHops_append_allowed_aux
    {g : RoomGraph} {start current next : RoomCoord}
    {hops : List RoomHop} (hvalid : ValidRoomHops g start hops)
    (hend : routeEnd start hops = current) {dir : Direction}
    (hedge : g.edge current dir next) :
    ValidRoomHops g start (hops ++ [(dir, next)]) := by
  induction hops generalizing start current next dir with
  | nil =>
      simp [routeEnd] at hend
      subst current
      simpa [ValidRoomHops] using hedge
  | cons hop rest ih =>
      rcases hop with ⟨firstDir, firstNext⟩
      simp only [ValidRoomHops] at hvalid
      simp only [routeEnd] at hend
      simp only [List.cons_append, ValidRoomHops]
      exact ⟨hvalid.1, ih hvalid.2 hend hedge⟩

theorem routeEnd_append_allowed_aux
    (start current next : RoomCoord) (hops : List RoomHop)
    (hend : routeEnd start hops = current) (dir : Direction) :
    routeEnd start (hops ++ [(dir, next)]) = next := by
  induction hops generalizing start with
  | nil => simp [routeEnd]
  | cons hop rest ih =>
      rcases hop with ⟨d, n⟩
      simp only [routeEnd] at hend
      simp only [List.cons_append, routeEnd]
      exact ih n hend

def extendAllowedRoute {g : RoomGraph} {start current next : RoomCoord}
    (route : RoomRoute g start current) (dir : Direction)
    (hedge : g.edge current dir next) : RoomRoute g start next where
  hops := route.hops ++ [(dir, next)]
  valid := validRoomHops_append_allowed_aux route.valid route.endsAt hedge
  endsAt := routeEnd_append_allowed_aux start current next route.hops
    route.endsAt dir

def emptyAllowedRoute (g : RoomGraph) (start : RoomCoord) :
    RoomRoute g start start where
  hops := []
  valid := by simp [ValidRoomHops]
  endsAt := by simp [routeEnd]

def RouteAllowed (ctx : RoomRoutingContext) : RoomCoord → List RoomHop → Prop
  | _, [] => True
  | room, (dir, next) :: rest =>
      roomEdgeAllowed ctx room dir = true ∧ RouteAllowed ctx next rest

def AllowedRoomReachable (g : RoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) : Prop :=
  ∃ route : RoomRoute g start target, RouteAllowed ctx start route.hops

theorem routeAllowed_append
    (ctx : RoomRoutingContext) {start current next : RoomCoord}
    {hops : List RoomHop} (hallowed : RouteAllowed ctx start hops)
    (hend : routeEnd start hops = current) {dir : Direction}
    (hnext : roomEdgeAllowed ctx current dir = true) :
    RouteAllowed ctx start (hops ++ [(dir, next)]) := by
  induction hops generalizing start current with
  | nil =>
      simp [routeEnd] at hend
      subst current
      simpa [RouteAllowed] using hnext
  | cons hop rest ih =>
      rcases hop with ⟨firstDir, firstNext⟩
      simp only [RouteAllowed] at hallowed
      simp only [routeEnd] at hend
      simp only [List.cons_append, RouteAllowed]
      exact ⟨hallowed.1, ih hallowed.2 hend hnext⟩

structure AllowedRoomBfsNode
    (g : RoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) where
  room : RoomCoord
  route : RoomRoute g start room
  allowed : RouteAllowed ctx start route.hops

def emptyAllowedRoomBfsNode (g : RoomGraph) (ctx : RoomRoutingContext)
    (start : RoomCoord) : AllowedRoomBfsNode g ctx start where
  room := start
  route := emptyAllowedRoute g start
  allowed := by simp [RouteAllowed, emptyAllowedRoute]

def expandAllowedRoomNode (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    {start : RoomCoord} (node : AllowedRoomBfsNode g.toRoomGraph ctx start) :
    List (AllowedRoomBfsNode g.toRoomGraph ctx start) :=
  (allowedRoomNeighbors g ctx node.room).map fun neighbor =>
    { room := neighbor.next
      route := extendAllowedRoute node.route neighbor.dir neighbor.edge_ok
      allowed := routeAllowed_append ctx node.allowed node.route.endsAt
        neighbor.allowed }

@[simp] theorem extendAllowedRoute_length
    {g : RoomGraph} {start current next : RoomCoord}
    (route : RoomRoute g start current) (dir : Direction)
    (hedge : g.edge current dir next) :
    (extendAllowedRoute route dir hedge).hops.length = route.hops.length + 1 := by
  simp [extendAllowedRoute]

theorem expandAllowedRoomNode_member_allowed
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (node child : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (_hmem : child ∈ expandAllowedRoomNode g ctx node) :
    RouteAllowed ctx start child.route.hops := child.allowed

theorem expandAllowedRoomNode_depth
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (node child : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (hmem : child ∈ expandAllowedRoomNode g ctx node) :
    child.route.hops.length = node.route.hops.length + 1 := by
  unfold expandAllowedRoomNode at hmem
  rw [List.mem_map] at hmem
  obtain ⟨neighbor, _, rfl⟩ := hmem
  simp

theorem expandAllowedRoomNode_contains_neighbor
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (node : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (dir : Direction) (next : RoomCoord)
    (hedge : g.edge node.room dir next)
    (hallowed : roomEdgeAllowed ctx node.room dir = true) :
    ∃ child ∈ expandAllowedRoomNode g ctx node, child.room = next := by
  obtain ⟨neighbor, hneighbor, hdir, hnext⟩ :=
    allowedRoomNeighbors_complete g ctx node.room dir next hedge hallowed
  let child : AllowedRoomBfsNode g.toRoomGraph ctx start := {
    room := neighbor.next
    route := extendAllowedRoute node.route neighbor.dir neighbor.edge_ok
    allowed := routeAllowed_append ctx node.allowed node.route.endsAt neighbor.allowed
  }
  refine ⟨child, ?_, ?_⟩
  · unfold expandAllowedRoomNode
    rw [List.mem_map]
    exact ⟨neighbor, hneighbor, rfl⟩
  · exact hnext

def enqueueAllowedFresh {g : RoomGraph} {ctx : RoomRoutingContext}
    {start : RoomCoord} :
    List (AllowedRoomBfsNode g ctx start) → List RoomCoord →
      List (AllowedRoomBfsNode g ctx start) × List RoomCoord
  | [], seen => ([], seen)
  | node :: rest, seen =>
      if seen.contains node.room then enqueueAllowedFresh rest seen
      else
        let result := enqueueAllowedFresh rest (node.room :: seen)
        (node :: result.1, result.2)

theorem enqueueAllowedFresh_nodes_subset
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord) (node : AllowedRoomBfsNode g ctx start),
      node ∈ (enqueueAllowedFresh candidates seen).1 → node ∈ candidates := by
  intro candidates
  induction candidates with
  | nil => intro seen node h; exact (List.not_mem_nil h).elim
  | cons head rest ih =>
      intro seen node h
      simp only [enqueueAllowedFresh] at h
      split at h
      · exact List.mem_cons_of_mem head (ih seen node h)
      · simp only [List.mem_cons] at h
        cases h with
        | inl heq => simp [heq]
        | inr hmem =>
            exact List.mem_cons_of_mem head
              (ih (head.room :: seen) node hmem)

theorem enqueueAllowedFresh_not_in_seen
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord) (node : AllowedRoomBfsNode g ctx start),
      node ∈ (enqueueAllowedFresh candidates seen).1 → node.room ∉ seen := by
  intro candidates
  induction candidates with
  | nil => intro seen node h; exact (List.not_mem_nil h).elim
  | cons head rest ih =>
      intro seen node h
      simp only [enqueueAllowedFresh] at h
      split at h
      · exact ih seen node h
      · rename_i hfresh
        simp only [List.mem_cons] at h
        cases h with
        | inl heq =>
            subst node
            simpa using hfresh
        | inr hmem =>
            have hn := ih (head.room :: seen) node hmem
            exact fun hs => hn (by simp [hs])

theorem enqueueAllowedFresh_seen_nodup
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord),
      seen.Nodup → (enqueueAllowedFresh candidates seen).2.Nodup := by
  intro candidates
  induction candidates with
  | nil => intro seen h; exact h
  | cons head rest ih =>
      intro seen hseen
      simp only [enqueueAllowedFresh]
      split
      · exact ih seen hseen
      · rename_i hfresh
        exact ih (head.room :: seen)
          (List.nodup_cons.mpr ⟨by simpa using hfresh, hseen⟩)

theorem enqueueAllowedFresh_seen_monotone
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord) (room : RoomCoord),
      room ∈ seen → room ∈ (enqueueAllowedFresh candidates seen).2 := by
  intro candidates
  induction candidates with
  | nil => intro seen room h; exact h
  | cons head rest ih =>
      intro seen room h
      simp only [enqueueAllowedFresh]
      split
      · exact ih seen room h
      · exact ih (head.room :: seen) room (by simp [h])

theorem enqueueAllowedFresh_output_registered
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord) (node : AllowedRoomBfsNode g ctx start),
      node ∈ (enqueueAllowedFresh candidates seen).1 →
      node.room ∈ (enqueueAllowedFresh candidates seen).2 := by
  intro candidates
  induction candidates with
  | nil => intro seen node h; exact (List.not_mem_nil h).elim
  | cons head rest ih =>
      intro seen node h
      by_cases hseen : head.room ∈ seen
      · simp [enqueueAllowedFresh, hseen] at h ⊢
        exact ih seen node h
      · simp [enqueueAllowedFresh, hseen] at h ⊢
        cases h with
        | inl heq =>
            subst node
            exact enqueueAllowedFresh_seen_monotone rest (head.room :: seen)
              head.room (by simp)
        | inr hmem => exact ih (head.room :: seen) node hmem

theorem enqueueAllowedFresh_candidate_registered
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord) (node : AllowedRoomBfsNode g ctx start),
      node ∈ candidates →
      node.room ∈ (enqueueAllowedFresh candidates seen).2 := by
  intro candidates
  induction candidates with
  | nil => intro seen node h; exact (List.not_mem_nil h).elim
  | cons head rest ih =>
      intro seen node h
      simp only [List.mem_cons] at h
      simp only [enqueueAllowedFresh]
      split
      · rename_i hheadSeen
        cases h with
        | inl heq =>
            subst node
            exact enqueueAllowedFresh_seen_monotone rest seen head.room
              (by simpa using hheadSeen)
        | inr hrest => exact ih seen node hrest
      · cases h with
        | inl heq =>
            subst node
            exact enqueueAllowedFresh_seen_monotone rest (head.room :: seen)
              head.room (by simp)
        | inr hrest => exact ih (head.room :: seen) node hrest

theorem enqueueAllowedFresh_length_balance
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord),
      (enqueueAllowedFresh candidates seen).2.length =
        seen.length + (enqueueAllowedFresh candidates seen).1.length := by
  intro candidates
  induction candidates with
  | nil => intro seen; simp [enqueueAllowedFresh]
  | cons head rest ih =>
      intro seen
      simp only [enqueueAllowedFresh]
      split
      · exact ih seen
      · have h := ih (head.room :: seen)
        simp only [List.length_cons] at h ⊢
        omega

theorem enqueueAllowedFresh_new_seen_has_output
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord) (room : RoomCoord),
      room ∈ (enqueueAllowedFresh candidates seen).2 →
      room ∈ seen ∨
        ∃ node ∈ (enqueueAllowedFresh candidates seen).1, node.room = room := by
  intro candidates
  induction candidates with
  | nil =>
      intro seen room h
      exact Or.inl h
  | cons head rest ih =>
      intro seen room h
      by_cases hfresh : head.room ∈ seen
      · simp [enqueueAllowedFresh, hfresh] at h ⊢
        exact ih seen room h
      · simp [enqueueAllowedFresh, hfresh] at h ⊢
        rcases ih (head.room :: seen) room h with hold | hnew
        · simp only [List.mem_cons] at hold
          cases hold with
          | inl heq =>
              exact Or.inr (Or.inl heq.symm)
          | inr hseen => exact Or.inl hseen
        · rcases hnew with ⟨node, hnode, heq⟩
          exact Or.inr (Or.inr ⟨node, hnode, heq⟩)

theorem enqueueAllowedFresh_candidate_output_of_not_seen
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g ctx start))
      (seen : List RoomCoord) (node : AllowedRoomBfsNode g ctx start),
      node ∈ candidates → node.room ∉ seen →
      ∃ found ∈ (enqueueAllowedFresh candidates seen).1,
        found.room = node.room := by
  intro candidates
  induction candidates with
  | nil => intro seen node h; exact (List.not_mem_nil h).elim
  | cons head rest ih =>
      intro seen node hmem hnot
      simp only [List.mem_cons] at hmem
      by_cases hhead : head.room ∈ seen
      · simp [enqueueAllowedFresh, hhead]
        cases hmem with
        | inl heq =>
            subst node
            exact (hnot hhead).elim
        | inr hrest => exact ih seen node hrest hnot
      · simp [enqueueAllowedFresh, hhead]
        cases hmem with
        | inl heq =>
            subst node
            exact Or.inl rfl
        | inr hrest =>
            by_cases heqRoom : node.room = head.room
            · exact Or.inl heqRoom.symm
            · obtain ⟨found, hfound, hroom⟩ :=
                ih (head.room :: seen) node hrest (by simp [hnot, heqRoom])
              exact Or.inr ⟨found, hfound, hroom⟩

def AllowedFrontierCovered
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (seen : List RoomCoord) (queue : List (AllowedRoomBfsNode g ctx start))
    (room : RoomCoord) : Prop :=
  room ∈ seen ∨ ∃ node ∈ queue, node.room = room

def AllowedExpanded (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (seen : List RoomCoord) (room : RoomCoord) : Prop :=
  ∀ dir next, g.edge room dir next →
    roomEdgeAllowed ctx room dir = true → next ∈ seen

def AllowedDiscoveryInvariant
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (seen : List RoomCoord)
    (queue : List (AllowedRoomBfsNode g.toRoomGraph ctx start)) : Prop :=
  ∀ room ∈ seen,
    AllowedExpanded g ctx seen room ∨
      ∃ node ∈ queue, node.room = room

/-- After expanding the queue head, every allowed outgoing neighbor is covered
by the successor state's `seen ∪ queue`. -/
theorem allowed_frontier_covers_expanded_neighbor
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (seen : List RoomCoord) (dir : Direction) (next : RoomCoord)
    (hedge : g.edge head.room dir next)
    (hallowed : roomEdgeAllowed ctx head.room dir = true) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen
    AllowedFrontierCovered
      added.2 (rest ++ added.1) next := by
  dsimp
  obtain ⟨child, hchild, hroom⟩ :=
    expandAllowedRoomNode_contains_neighbor g ctx head dir next hedge hallowed
  exact Or.inl (by
    rw [← hroom]
    exact enqueueAllowedFresh_candidate_registered _ seen child hchild)

theorem allowedDiscoveryInvariant_initial
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) :
    AllowedDiscoveryInvariant g ctx [start]
      [emptyAllowedRoomBfsNode g.toRoomGraph ctx start] := by
  intro room hroom
  right
  simp at hroom
  subst room
  exact ⟨emptyAllowedRoomBfsNode g.toRoomGraph ctx start, by simp, rfl⟩

theorem allowedDiscoveryInvariant_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (seen : List RoomCoord)
    (hinv : AllowedDiscoveryInvariant g ctx seen (head :: rest)) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen
    AllowedDiscoveryInvariant g ctx added.2 (rest ++ added.1) := by
  dsimp
  let candidates := expandAllowedRoomNode g ctx head
  let added := enqueueAllowedFresh candidates seen
  intro room hroom
  rcases enqueueAllowedFresh_new_seen_has_output candidates seen room hroom with
    hold | houtput
  · rcases hinv room hold with hexp | hqueued
    · left
      intro dir next hedge hallowed
      exact enqueueAllowedFresh_seen_monotone candidates seen next
        (hexp dir next hedge hallowed)
    · rcases hqueued with ⟨node, hnode, hnroom⟩
      simp only [List.mem_cons] at hnode
      cases hnode with
      | inl heq =>
          subst node
          subst room
          left
          intro dir next hedge hallowed
          obtain ⟨child, hchild, hchildRoom⟩ :=
            expandAllowedRoomNode_contains_neighbor
              g ctx head dir next hedge hallowed
          rw [← hchildRoom]
          exact enqueueAllowedFresh_candidate_registered candidates seen child
            (by simpa [candidates] using hchild)
      | inr hrest =>
          right
          exact ⟨node, by simp [hrest], hnroom⟩
  · rcases houtput with ⟨node, hnode, hnroom⟩
    right
    exact ⟨node, List.mem_append.mpr (Or.inr (by
      simpa [candidates] using hnode)), hnroom⟩

def AllowedTargetQueued
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (target : RoomCoord) (seen : List RoomCoord)
    (queue : List (AllowedRoomBfsNode g ctx start)) : Prop :=
  target ∈ seen → ∃ node ∈ queue, node.room = target

theorem allowedTargetQueued_initial
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) :
    AllowedTargetQueued (g := g.toRoomGraph) (ctx := ctx) target [start]
      [emptyAllowedRoomBfsNode g.toRoomGraph ctx start] := by
  intro htarget
  simp at htarget
  subst target
  exact ⟨emptyAllowedRoomBfsNode g.toRoomGraph ctx start, by simp, rfl⟩

theorem allowedTargetQueued_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (target : RoomCoord)
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (seen : List RoomCoord)
    (hne : head.room ≠ target)
    (hinv : AllowedTargetQueued target seen (head :: rest)) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen
    AllowedTargetQueued target added.2 (rest ++ added.1) := by
  dsimp
  let candidates := expandAllowedRoomNode g ctx head
  intro htarget
  rcases enqueueAllowedFresh_new_seen_has_output candidates seen target htarget with
    hold | houtput
  · obtain ⟨node, hnode, hroom⟩ := hinv hold
    simp only [List.mem_cons] at hnode
    cases hnode with
    | inl heq =>
        subst node
        exact (hne hroom).elim
    | inr hrest =>
        exact ⟨node, List.mem_append.mpr (Or.inl hrest), hroom⟩
  · obtain ⟨node, hnode, hroom⟩ := houtput
    exact ⟨node, List.mem_append.mpr (Or.inr (by
      simpa [candidates] using hnode)), hroom⟩

theorem allowed_route_end_mem_of_closed
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (seen : List RoomCoord)
    (hclosed : ∀ room ∈ seen, AllowedExpanded g ctx seen room) :
    ∀ (current : RoomCoord) (hops : List RoomHop),
      ValidRoomHops g.toRoomGraph current hops →
      RouteAllowed ctx current hops →
      current ∈ seen → routeEnd current hops ∈ seen := by
  intro current hops
  induction hops generalizing current with
  | nil => intro _ _ hcurrent; simpa [routeEnd] using hcurrent
  | cons hop rest ih =>
      rcases hop with ⟨dir, next⟩
      intro hvalid hallowed hcurrent
      simp only [ValidRoomHops] at hvalid
      simp only [RouteAllowed] at hallowed
      have hnext : next ∈ seen :=
        hclosed current hcurrent dir next hvalid.1 hallowed.1
      simp only [routeEnd]
      exact ih next hvalid.2 hallowed.2 hnext

theorem allowed_route_target_mem_of_closed
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    {start target : RoomCoord} (route : RoomRoute g.toRoomGraph start target)
    (hallowed : RouteAllowed ctx start route.hops)
    (seen : List RoomCoord) (hstart : start ∈ seen)
    (hclosed : ∀ room ∈ seen, AllowedExpanded g ctx seen room) :
    target ∈ seen := by
  have hend := allowed_route_end_mem_of_closed g ctx seen hclosed
    start route.hops route.valid hallowed hstart
  simpa [route.endsAt] using hend

def AllowedNodesAtDepth {g : RoomGraph} {ctx : RoomRoutingContext}
    {start : RoomCoord} (nodes : List (AllowedRoomBfsNode g ctx start))
    (depth : Nat) : Prop :=
  ∀ node ∈ nodes, node.route.hops.length = depth

theorem enqueueAllowedFresh_preserves_depth
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (candidates : List (AllowedRoomBfsNode g ctx start))
    (seen : List RoomCoord) (depth : Nat)
    (hdepth : AllowedNodesAtDepth candidates depth) :
    AllowedNodesAtDepth (enqueueAllowedFresh candidates seen).1 depth := by
  intro node hnode
  exact hdepth node (enqueueAllowedFresh_nodes_subset candidates seen node hnode)

theorem allowed_expansion_at_next_depth
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (node : AllowedRoomBfsNode g.toRoomGraph ctx start) (seen : List RoomCoord) :
    AllowedNodesAtDepth
      (enqueueAllowedFresh (expandAllowedRoomNode g ctx node) seen).1
      (node.route.hops.length + 1) := by
  apply enqueueAllowedFresh_preserves_depth
  intro child hchild
  exact expandAllowedRoomNode_depth g ctx node child hchild

theorem allowedNodesAtDepth_append
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    {xs ys : List (AllowedRoomBfsNode g ctx start)} {depth : Nat}
    (hxs : AllowedNodesAtDepth xs depth)
    (hys : AllowedNodesAtDepth ys depth) :
    AllowedNodesAtDepth (xs ++ ys) depth := by
  intro node hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl hx => exact hxs node hx
  | inr hy => exact hys node hy

/-- A FIFO queue contains only the current layer and the immediately following
layer.  This is stronger and easier to preserve than arbitrary sortedness. -/
def AllowedQueueLayered
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (queue : List (AllowedRoomBfsNode g ctx start)) (depth : Nat) : Prop :=
  ∃ current next,
    queue = current ++ next ∧
    AllowedNodesAtDepth current depth ∧
    AllowedNodesAtDepth next (depth + 1)

theorem allowedQueueLayered_initial
    (g : RoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) :
    AllowedQueueLayered [emptyAllowedRoomBfsNode g ctx start] 0 := by
  refine ⟨[emptyAllowedRoomBfsNode g ctx start], [], by simp, ?_, ?_⟩
  · intro node hnode
    simp at hnode
    subst node
    rfl
  · intro node hnode
    exact (List.not_mem_nil hnode).elim

/-- While current-layer nodes remain, processing its head appends only
next-layer nodes and preserves the two-layer queue decomposition. -/
theorem allowedQueueLayered_process_current
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (current next : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (seen : List RoomCoord) (depth : Nat)
    (hhead : head.route.hops.length = depth)
    (hcurrent : AllowedNodesAtDepth current depth)
    (hnext : AllowedNodesAtDepth next (depth + 1)) :
    AllowedQueueLayered
      (current ++ next ++
        (enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen).1)
      depth := by
  let children :=
    (enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen).1
  have hchildren : AllowedNodesAtDepth children (depth + 1) := by
    have h := allowed_expansion_at_next_depth g ctx head seen
    simpa [children, hhead] using h
  refine ⟨current, next ++ children, ?_, hcurrent,
    allowedNodesAtDepth_append hnext hchildren⟩
  simp [children, List.append_assoc]

/-- Once the current layer is empty, the next layer becomes the new current
layer at depth `d+1`. -/
theorem allowedQueueLayered_advance
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (next : List (AllowedRoomBfsNode g ctx start)) (depth : Nat)
    (hnext : AllowedNodesAtDepth next (depth + 1)) :
    AllowedQueueLayered next (depth + 1) := by
  refine ⟨next, [], by simp, hnext, ?_⟩
  intro node hnode
  exact (List.not_mem_nil hnode).elim

theorem allowedQueueLayered_node_depth
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    {queue : List (AllowedRoomBfsNode g ctx start)} {depth : Nat}
    (hlayered : AllowedQueueLayered queue depth)
    (node : AllowedRoomBfsNode g ctx start) (hnode : node ∈ queue) :
    node.route.hops.length = depth ∨
      node.route.hops.length = depth + 1 := by
  rcases hlayered with ⟨current, next, hqueue, hcurrent, hnext⟩
  rw [hqueue, List.mem_append] at hnode
  cases hnode with
  | inl h => exact Or.inl (hcurrent node h)
  | inr h => exact Or.inr (hnext node h)

theorem allowedQueueLayered_current_le_all
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    {queue : List (AllowedRoomBfsNode g ctx start)} {depth : Nat}
    (hlayered : AllowedQueueLayered queue depth)
    (currentNode other : AllowedRoomBfsNode g ctx start)
    (hcurrentDepth : currentNode.route.hops.length = depth)
    (hother : other ∈ queue) :
    currentNode.route.hops.length ≤ other.route.hops.length := by
  rcases allowedQueueLayered_node_depth hlayered other hother with h | h
  · omega
  · omega

theorem allowedQueueLayered_no_shallower
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    {queue : List (AllowedRoomBfsNode g ctx start)} {depth : Nat}
    (hlayered : AllowedQueueLayered queue depth) :
    ∀ node ∈ queue, depth ≤ node.route.hops.length := by
  intro node hnode
  rcases allowedQueueLayered_node_depth hlayered node hnode with h | h
  · omega
  · omega

def AllowedQueueBreadthOrdered
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (queue : List (AllowedRoomBfsNode g ctx start)) : Prop :=
  queue.Pairwise (fun a b => a.route.hops.length ≤ b.route.hops.length) ∧
  match queue with
  | [] => True
  | head :: _ => ∀ node ∈ queue,
      node.route.hops.length ≤ head.route.hops.length + 1

theorem allowedNodesAtDepth_pairwise
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (nodes : List (AllowedRoomBfsNode g ctx start)) (depth : Nat)
    (hdepth : AllowedNodesAtDepth nodes depth) :
    nodes.Pairwise (fun a b => a.route.hops.length ≤ b.route.hops.length) := by
  induction nodes with
  | nil => simp
  | cons head rest ih =>
      rw [List.pairwise_cons]
      constructor
      · intro node hnode
        rw [hdepth head (by simp), hdepth node (by simp [hnode])]
        omega
      · apply ih
        intro node hnode
        exact hdepth node (by simp [hnode])

theorem allowedQueueBreadthOrdered_initial
    (g : RoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) :
    AllowedQueueBreadthOrdered
      [emptyAllowedRoomBfsNode g ctx start] := by
  constructor
  · simp
  · intro node hnode
    simp at hnode
    subst node
    omega

theorem allowedQueueBreadthOrdered_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (seen : List RoomCoord)
    (hordered : AllowedQueueBreadthOrdered (head :: rest)) :
    let children :=
      (enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen).1
    AllowedQueueBreadthOrdered (rest ++ children) := by
  dsimp
  let children :=
    (enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen).1
  have hchildrenDepth := allowed_expansion_at_next_depth g ctx head seen
  have hchildrenPair := allowedNodesAtDepth_pairwise children
    (head.route.hops.length + 1) (by simpa [children] using hchildrenDepth)
  have hpair := (List.pairwise_cons.mp hordered.1)
  have hrestPair := hpair.2
  have hcross : ∀ a ∈ rest, ∀ b ∈ children,
      a.route.hops.length ≤ b.route.hops.length := by
    intro a ha b hb
    have haBound := hordered.2 a (by simp [ha])
    have hbDepth := hchildrenDepth b (by simpa [children] using hb)
    omega
  constructor
  · exact List.pairwise_append.mpr ⟨hrestPair, hchildrenPair, hcross⟩
  · cases hrest : rest with
    | nil =>
        simp only [List.nil_append]
        cases hchildren :
            (enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen).1 with
        | nil => trivial
        | cons child tail =>
            intro node hnode
            have hn := hchildrenDepth node (by rw [hchildren]; exact hnode)
            have hc := hchildrenDepth child (by rw [hchildren]; simp)
            omega
    | cons first tail =>
        change ∀ node ∈ (first :: tail) ++
            (enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen).1,
          node.route.hops.length ≤ first.route.hops.length + 1
        intro node hnode
        have hheadFirst := hpair.1 first (by simp [hrest])
        rw [List.mem_append] at hnode
        cases hnode with
        | inl hnrest =>
            have hnBound := hordered.2 node (by simp [hrest, hnrest])
            omega
        | inr hnchild =>
            have hnDepth := hchildrenDepth node hnchild
            omega

structure AllowedRoomBfsState
    (g : RoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) where
  queue : List (AllowedRoomBfsNode g ctx start)
  seen : List RoomCoord
  processed : List (AllowedRoomBfsNode g ctx start) := []

def AllowedHistoryCoverage
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (state : AllowedRoomBfsState g ctx start) : Prop :=
  ∀ room ∈ state.seen,
    ∃ node ∈ state.processed ++ state.queue, node.room = room

def AllowedProcessedLeQueue
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (state : AllowedRoomBfsState g ctx start) : Prop :=
  match state.queue with
  | [] => True
  | head :: _ => ∀ node ∈ state.processed,
      node.route.hops.length ≤ head.route.hops.length

def AllowedProcessedExpanded
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start) : Prop :=
  ∀ node ∈ state.processed, AllowedExpanded g ctx state.seen node.room

def AllowedProcessedEdgeBound
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start) : Prop :=
  ∀ node ∈ state.processed, ∀ dir next,
    g.edge node.room dir next → roomEdgeAllowed ctx node.room dir = true →
    ∃ found ∈ state.processed ++ state.queue,
      found.room = next ∧
      found.route.hops.length ≤ node.route.hops.length + 1

def AllowedTargetNotProcessed
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (target : RoomCoord) (state : AllowedRoomBfsState g ctx start) : Prop :=
  ∀ node ∈ state.processed, node.room ≠ target

def AllowedStateInvariant
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start) : Prop :=
  state.seen.Nodup ∧
  (∀ room ∈ state.seen, room ∈ g.rooms) ∧
  (∀ node ∈ state.queue, node.room ∈ state.seen)

theorem nodup_length_le_of_subset_rooms (xs ys : List RoomCoord)
    (hx : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      have ha : a ∈ ys := hsub a (by simp)
      have hparts : a ∉ xs ∧ xs.Nodup := by simpa using hx
      have hsubErase : ∀ x ∈ xs, x ∈ ys.erase a := by
        intro x hxmem
        have hxy : x ∈ ys := hsub x (by simp [hxmem])
        have hne : x ≠ a := by
          intro heq
          subst x
          exact hparts.1 hxmem
        exact (List.mem_erase_of_ne hne).2 hxy
      have hle := ih (ys.erase a) hparts.2 hsubErase
      rw [List.length_erase_of_mem ha] at hle
      have hypos : 0 < ys.length := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

theorem allowedStateInvariant_seen_length
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (hinv : AllowedStateInvariant g ctx state) :
    state.seen.length ≤ g.rooms.length := by
  exact nodup_length_le_of_subset_rooms state.seen g.rooms hinv.1 hinv.2.1

theorem expandAllowedRoomNode_rooms
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (node : AllowedRoomBfsNode g.toRoomGraph ctx start) :
    ∀ child ∈ expandAllowedRoomNode g ctx node, child.room ∈ g.rooms := by
  intro child hchild
  unfold expandAllowedRoomNode at hchild
  rw [List.mem_map] at hchild
  obtain ⟨neighbor, _, rfl⟩ := hchild
  exact (g.edge_rooms node.room neighbor.dir neighbor.next neighbor.edge_ok).2

theorem enqueueAllowedFresh_seen_subset_rooms
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord} :
    ∀ (candidates : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
      (seen : List RoomCoord),
      (∀ room ∈ seen, room ∈ g.rooms) →
      (∀ node ∈ candidates, node.room ∈ g.rooms) →
      ∀ room ∈ (enqueueAllowedFresh candidates seen).2, room ∈ g.rooms := by
  intro candidates
  induction candidates with
  | nil => intro seen hseen _ room hroom; exact hseen room hroom
  | cons head rest ih =>
      intro seen hseen hcandidates
      simp only [enqueueAllowedFresh]
      split
      · apply ih seen hseen
        intro node hnode
        exact hcandidates node (by simp [hnode])
      · apply ih (head.room :: seen)
        · intro room hroom
          simp only [List.mem_cons] at hroom
          cases hroom with
          | inl heq => simpa [← heq] using hcandidates head (by simp)
          | inr hmem => exact hseen room hmem
        · intro node hnode
          exact hcandidates node (by simp [hnode])

theorem allowedStateInvariant_initial
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord)
    (hstart : start ∈ g.rooms) :
    AllowedStateInvariant g ctx {
      queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start]
      seen := [start]
    } := by
  refine ⟨by simp, ?_, ?_⟩
  · intro room hroom
    simp at hroom
    subst room
    exact hstart
  · intro node hnode
    simp at hnode
    subst node
    simp [emptyAllowedRoomBfsNode]

theorem allowedHistoryCoverage_initial
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) :
    AllowedHistoryCoverage
      ({ queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start],
         seen := [start] } : AllowedRoomBfsState g.toRoomGraph ctx start) := by
  intro room hroom
  simp at hroom
  subst room
  exact ⟨emptyAllowedRoomBfsNode g.toRoomGraph ctx start, by simp, rfl⟩

theorem allowedProcessedLeQueue_initial
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) :
    AllowedProcessedLeQueue
      ({ queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start],
         seen := [start] } : AllowedRoomBfsState g.toRoomGraph ctx start) := by
  simp [AllowedProcessedLeQueue]

theorem allowedProcessedExpanded_initial
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) :
    AllowedProcessedExpanded g ctx
      ({ queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start],
         seen := [start] } : AllowedRoomBfsState g.toRoomGraph ctx start) := by
  intro node hnode
  exact (List.not_mem_nil hnode).elim

theorem allowedProcessedEdgeBound_initial
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (start : RoomCoord) :
    AllowedProcessedEdgeBound g ctx
      ({ queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start],
         seen := [start] } : AllowedRoomBfsState g.toRoomGraph ctx start) := by
  intro node hnode
  exact (List.not_mem_nil hnode).elim

theorem allowedTargetNotProcessed_initial
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) :
    AllowedTargetNotProcessed target
      ({ queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start],
         seen := [start] } : AllowedRoomBfsState g.toRoomGraph ctx start) := by
  intro node hnode
  exact (List.not_mem_nil hnode).elim

theorem allowedHistoryMember_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (hqueue : state.queue = head :: rest)
    (node : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (hnode : node ∈ state.processed ++ state.queue) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) state.seen
    node ∈ (head :: state.processed) ++ (rest ++ added.1) := by
  dsimp
  rw [hqueue] at hnode
  rw [List.mem_append] at hnode
  cases hnode with
  | inl hp => simp [hp]
  | inr hq =>
      simp only [List.mem_cons] at hq
      cases hq with
      | inl hh => subst node; simp
      | inr hr => simp [hr]

theorem allowedTargetNotProcessed_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (target : RoomCoord)
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (_hqueue : state.queue = head :: rest)
    (hne : head.room ≠ target)
    (hinv : AllowedTargetNotProcessed target state) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) state.seen
    AllowedTargetNotProcessed target
      ({ queue := rest ++ added.1, seen := added.2,
         processed := head :: state.processed } :
        AllowedRoomBfsState g.toRoomGraph ctx start) := by
  dsimp
  intro node hnode
  simp only [List.mem_cons] at hnode
  cases hnode with
  | inl hh => subst node; exact hne
  | inr hp => exact hinv node hp

theorem allowedHistoryCoverage_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (hqueue : state.queue = head :: rest)
    (hinv : AllowedHistoryCoverage state) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) state.seen
    AllowedHistoryCoverage
      ({ queue := rest ++ added.1, seen := added.2,
         processed := head :: state.processed } :
        AllowedRoomBfsState g.toRoomGraph ctx start) := by
  dsimp
  let candidates := expandAllowedRoomNode g ctx head
  intro room hroom
  rcases enqueueAllowedFresh_new_seen_has_output candidates state.seen room hroom with
    hold | hnew
  · obtain ⟨node, hnode, hnroom⟩ := hinv room hold
    rw [hqueue] at hnode
    rw [List.mem_append] at hnode
    cases hnode with
    | inl hp =>
        exact ⟨node, by simp [hp], hnroom⟩
    | inr hq =>
        simp only [List.mem_cons] at hq
        cases hq with
        | inl hh =>
            subst node
            exact ⟨head, by simp, hnroom⟩
        | inr hr =>
            exact ⟨node, by simp [hr], hnroom⟩
  · obtain ⟨node, hnode, hnroom⟩ := hnew
    exact ⟨node, by
      rw [List.mem_append]
      exact Or.inr (List.mem_append.mpr (Or.inr (by
        simpa [candidates] using hnode))), hnroom⟩

theorem allowedProcessedLeQueue_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (hqueue : state.queue = head :: rest)
    (hle : AllowedProcessedLeQueue state)
    (hordered : AllowedQueueBreadthOrdered state.queue) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) state.seen
    AllowedProcessedLeQueue
      ({ queue := rest ++ added.1, seen := added.2,
         processed := head :: state.processed } :
        AllowedRoomBfsState g.toRoomGraph ctx start) := by
  dsimp
  have horderedHead : AllowedQueueBreadthOrdered (head :: rest) := by
    simpa [hqueue] using hordered
  have hheadLe := (List.pairwise_cons.mp horderedHead.1).1
  have hleHead : ∀ node ∈ state.processed,
      node.route.hops.length ≤ head.route.hops.length := by
    simpa [AllowedProcessedLeQueue, hqueue] using hle
  let children :=
    (enqueueAllowedFresh (expandAllowedRoomNode g ctx head) state.seen).1
  have hchildrenDepth := allowed_expansion_at_next_depth g ctx head state.seen
  cases hrest : rest with
  | cons first tail =>
      simp only [List.cons_append, AllowedProcessedLeQueue]
      intro node hnode
      simp only [List.mem_cons] at hnode
      have hhf := hheadLe first (by simp [hrest])
      cases hnode with
      | inl hn =>
          subst node
          exact hhf
      | inr hp => exact Nat.le_trans (hleHead node hp) hhf
  | nil =>
      simp only [List.nil_append]
      cases hc : children with
      | nil =>
          rw [show (enqueueAllowedFresh
            (expandAllowedRoomNode g ctx head) state.seen).1 = children from rfl, hc]
          trivial
      | cons child tail =>
          rw [show (enqueueAllowedFresh
            (expandAllowedRoomNode g ctx head) state.seen).1 = children from rfl, hc]
          simp only [AllowedProcessedLeQueue]
          have hchildDepth := hchildrenDepth child (by
            rw [show (enqueueAllowedFresh
              (expandAllowedRoomNode g ctx head) state.seen).1 = children from rfl, hc]
            simp)
          intro node hnode
          simp only [List.mem_cons] at hnode
          cases hnode with
          | inl hn => subst node; omega
          | inr hp => exact Nat.le_trans (hleHead node hp) (by omega)

theorem allowedProcessedExpanded_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (_hqueue : state.queue = head :: rest)
    (hinv : AllowedProcessedExpanded g ctx state) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) state.seen
    AllowedProcessedExpanded g ctx
      ({ queue := rest ++ added.1, seen := added.2,
         processed := head :: state.processed } :
        AllowedRoomBfsState g.toRoomGraph ctx start) := by
  dsimp
  let candidates := expandAllowedRoomNode g ctx head
  intro node hnode
  simp only [List.mem_cons] at hnode
  cases hnode with
  | inl heq =>
      subst node
      intro dir next hedge hallowed
      obtain ⟨child, hchild, hroom⟩ :=
        expandAllowedRoomNode_contains_neighbor g ctx head dir next hedge hallowed
      rw [← hroom]
      exact enqueueAllowedFresh_candidate_registered candidates state.seen child
        (by simpa [candidates] using hchild)
  | inr hp =>
      intro dir next hedge hallowed
      exact enqueueAllowedFresh_seen_monotone candidates state.seen next
        (hinv node hp dir next hedge hallowed)

theorem allowedProcessedEdgeBound_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (hqueue : state.queue = head :: rest)
    (hbound : AllowedProcessedEdgeBound g ctx state)
    (hhistory : AllowedHistoryCoverage state)
    (hprocessedLe : AllowedProcessedLeQueue state)
    (hordered : AllowedQueueBreadthOrdered state.queue) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) state.seen
    AllowedProcessedEdgeBound g ctx
      ({ queue := rest ++ added.1, seen := added.2,
         processed := head :: state.processed } :
        AllowedRoomBfsState g.toRoomGraph ctx start) := by
  dsimp
  let candidates := expandAllowedRoomNode g ctx head
  let added := enqueueAllowedFresh candidates state.seen
  have horderedHead : AllowedQueueBreadthOrdered (head :: rest) := by
    simpa [hqueue] using hordered
  have hprocessedHead : ∀ node ∈ state.processed,
      node.route.hops.length ≤ head.route.hops.length := by
    simpa [AllowedProcessedLeQueue, hqueue] using hprocessedLe
  intro node hnode dir next hedge hallowed
  simp only [List.mem_cons] at hnode
  cases hnode with
  | inr hp =>
      obtain ⟨found, hfound, hroom, hlen⟩ :=
        hbound node hp dir next hedge hallowed
      refine ⟨found, ?_, hroom, hlen⟩
      rw [hqueue] at hfound
      rw [List.mem_append] at hfound
      cases hfound with
      | inl hproc => exact by simp [hproc]
      | inr hq =>
          simp only [List.mem_cons] at hq
          cases hq with
          | inl hh => subst found; simp
          | inr hr =>
              rw [List.mem_append]
              exact Or.inr (List.mem_append.mpr (Or.inl hr))
  | inl heq =>
      subst node
      obtain ⟨child, hchild, hchildRoom⟩ :=
        expandAllowedRoomNode_contains_neighbor g ctx head dir next hedge hallowed
      by_cases hseen : next ∈ state.seen
      · obtain ⟨found, hfound, hfoundRoom⟩ := hhistory next hseen
        have hlen : found.route.hops.length ≤ head.route.hops.length + 1 := by
          rw [hqueue] at hfound
          rw [List.mem_append] at hfound
          cases hfound with
          | inl hp => exact Nat.le_trans (hprocessedHead found hp) (by omega)
          | inr hq => exact horderedHead.2 found hq
        refine ⟨found, ?_, hfoundRoom, hlen⟩
        rw [hqueue] at hfound
        rw [List.mem_append] at hfound
        cases hfound with
        | inl hp => exact by simp [hp]
        | inr hq =>
            simp only [List.mem_cons] at hq
            cases hq with
            | inl hh => subst found; simp
            | inr hr =>
                rw [List.mem_append]
                exact Or.inr (List.mem_append.mpr (Or.inl hr))
      · obtain ⟨found, hfound, hfoundRoom⟩ :=
          enqueueAllowedFresh_candidate_output_of_not_seen
            candidates state.seen child
            (by simpa [candidates] using hchild)
            (by simpa [hchildRoom] using hseen)
        have hfoundCandidate : found ∈ candidates :=
          enqueueAllowedFresh_nodes_subset candidates state.seen found hfound
        have hfoundDepth := expandAllowedRoomNode_depth g ctx head found
          (by simpa [candidates] using hfoundCandidate)
        refine ⟨found, ?_, ?_, by omega⟩
        · rw [List.mem_append]
          exact Or.inr (List.mem_append.mpr (Or.inr (by
            simpa [added] using hfound)))
        · exact hfoundRoom.trans hchildRoom

theorem allowed_queue_head_le_member
    {g : RoomGraph} {ctx : RoomRoutingContext} {start : RoomCoord}
    (head : AllowedRoomBfsNode g ctx start)
    (rest : List (AllowedRoomBfsNode g ctx start))
    (hordered : AllowedQueueBreadthOrdered (head :: rest))
    (node : AllowedRoomBfsNode g ctx start) (hnode : node ∈ head :: rest) :
    head.route.hops.length ≤ node.route.hops.length := by
  simp only [List.mem_cons] at hnode
  cases hnode with
  | inl heq => subst node; exact Nat.le_refl _
  | inr hr => exact (List.pairwise_cons.mp hordered.1).1 node hr

theorem allowed_queue_head_le_route_from_history
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start target : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (hqueue : state.queue = head :: rest)
    (hordered : AllowedQueueBreadthOrdered state.queue)
    (hedgeBound : AllowedProcessedEdgeBound g ctx state)
    (htargetNotProcessed : AllowedTargetNotProcessed target state) :
    ∀ (current : RoomCoord) (hops : List RoomHop) (bound : Nat)
      (witness : AllowedRoomBfsNode g.toRoomGraph ctx start),
      ValidRoomHops g.toRoomGraph current hops →
      RouteAllowed ctx current hops →
      routeEnd current hops = target →
      witness ∈ state.processed ++ state.queue →
      witness.room = current →
      witness.route.hops.length ≤ bound →
      head.route.hops.length ≤ bound + hops.length := by
  intro current hops
  induction hops generalizing current with
  | nil =>
      intro bound witness _ _ hend hwitness hwroom hwlen
      simp only [routeEnd] at hend
      subst current
      rw [List.mem_append] at hwitness
      cases hwitness with
      | inl hp =>
          exfalso
          exact htargetNotProcessed witness hp hwroom
      | inr hq =>
          have horderedHead : AllowedQueueBreadthOrdered (head :: rest) := by
            simpa [hqueue] using hordered
          have hheadLe := allowed_queue_head_le_member head rest horderedHead witness
            (by simpa [hqueue] using hq)
          simp only [List.length_nil, Nat.add_zero]
          exact Nat.le_trans hheadLe hwlen
  | cons hop tail ih =>
      rcases hop with ⟨dir, next⟩
      intro bound witness hvalid hallowed hend hwitness hwroom hwlen
      simp only [ValidRoomHops] at hvalid
      simp only [RouteAllowed] at hallowed
      rw [List.mem_append] at hwitness
      cases hwitness with
      | inr hq =>
          have horderedHead : AllowedQueueBreadthOrdered (head :: rest) := by
            simpa [hqueue] using hordered
          have hheadLe := allowed_queue_head_le_member head rest horderedHead witness
            (by simpa [hqueue] using hq)
          simp only [List.length_cons]
          omega
      | inl hp =>
          obtain ⟨found, hfound, hfoundRoom, hfoundLen⟩ :=
            hedgeBound witness hp dir next (by simpa [hwroom] using hvalid.1)
              (by simpa [hwroom] using hallowed.1)
          have hfoundBound : found.route.hops.length ≤ bound + 1 := by omega
          have hr := ih next (bound + 1) found hvalid.2 hallowed.2
            (by simpa [routeEnd] using hend) hfound hfoundRoom hfoundBound
          simp only [List.length_cons]
          omega

theorem allowedStateInvariant_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (seen : List RoomCoord)
    (hinv : AllowedStateInvariant g ctx { queue := head :: rest, seen := seen }) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen
    AllowedStateInvariant g ctx { queue := rest ++ added.1, seen := added.2 } := by
  dsimp
  rcases hinv with ⟨hnd, hseenRooms, hqueueSeen⟩
  have hcandidates := expandAllowedRoomNode_rooms g ctx head
  refine ⟨enqueueAllowedFresh_seen_nodup _ seen hnd, ?_, ?_⟩
  · exact enqueueAllowedFresh_seen_subset_rooms g ctx _ seen hseenRooms hcandidates
  · intro node hnode
    rw [List.mem_append] at hnode
    cases hnode with
    | inl hrest =>
        apply enqueueAllowedFresh_seen_monotone _ seen node.room
        exact hqueueSeen node (by simp [hrest])
    | inr hfresh =>
        exact enqueueAllowedFresh_output_registered _ seen node hfresh

def allowedStateMeasure
    (g : FiniteRoomGraph) {ctx : RoomRoutingContext} {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start) : Nat :=
  g.rooms.length - state.seen.length + state.queue.length

theorem allowedStateMeasure_step
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) {start : RoomCoord}
    (head : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (rest : List (AllowedRoomBfsNode g.toRoomGraph ctx start))
    (seen : List RoomCoord)
    (hinv : AllowedStateInvariant g ctx { queue := head :: rest, seen := seen }) :
    let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen
    allowedStateMeasure g
      ({ queue := rest ++ added.1, seen := added.2 } :
        AllowedRoomBfsState g.toRoomGraph ctx start) + 1 =
    allowedStateMeasure g
      ({ queue := head :: rest, seen := seen } :
        AllowedRoomBfsState g.toRoomGraph ctx start) := by
  dsimp [allowedStateMeasure]
  let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) seen
  have hbalance : added.2.length = seen.length + added.1.length := by
    exact enqueueAllowedFresh_length_balance _ seen
  have hold : seen.length ≤ g.rooms.length :=
    allowedStateInvariant_seen_length g ctx _ hinv
  have hnextInv := allowedStateInvariant_step g ctx head rest seen hinv
  have hnew : added.2.length ≤ g.rooms.length :=
    allowedStateInvariant_seen_length g ctx _ hnextInv
  have harith :
      (g.rooms.length - added.2.length) +
          (rest.length + added.1.length) + 1 =
        (g.rooms.length - seen.length) + (rest.length + 1) := by
    omega
  simpa [added, List.length_append, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using harith

/-- Total executable FIFO.  Termination is justified by the finite-state
measure rather than exposed as an arbitrary fuel parameter. -/
def allowedRoomBfsTotalSearch
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (target : RoomCoord)
    {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (hinv : AllowedStateInvariant g ctx state) :
    Option (AllowedRoomBfsNode g.toRoomGraph ctx start) :=
  match hqueue : state.queue with
  | [] => none
  | head :: rest =>
      if head.room = target then some head
      else
        let added := enqueueAllowedFresh (expandAllowedRoomNode g ctx head) state.seen
        let next : AllowedRoomBfsState g.toRoomGraph ctx start :=
          { queue := rest ++ added.1, seen := added.2,
            processed := head :: state.processed }
        allowedRoomBfsTotalSearch g ctx target next
          (by
            have hinvHead : AllowedStateInvariant g ctx
                { queue := head :: rest, seen := state.seen } := by
              simpa [AllowedStateInvariant, hqueue] using hinv
            simpa [AllowedStateInvariant, next, added] using
              allowedStateInvariant_step g ctx head rest state.seen hinvHead)
termination_by allowedStateMeasure g state
decreasing_by
  have hinvHead : AllowedStateInvariant g ctx
      { queue := head :: rest, seen := state.seen } := by
    simpa [AllowedStateInvariant, hqueue] using hinv
  have hm := allowedStateMeasure_step g ctx head rest state.seen hinvHead
  simp [allowedStateMeasure, hqueue] at hm ⊢
  omega

def allowedRoomBfsTotal
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms) :
    Option (AllowedRoomBfsNode g.toRoomGraph ctx start) :=
  allowedRoomBfsTotalSearch g ctx target
    { queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start], seen := [start] }
    (allowedStateInvariant_initial g ctx start hstart)

theorem allowedRoomBfsTotalSearch_returns_target
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (target : RoomCoord)
    {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (hinv : AllowedStateInvariant g ctx state)
    {node : AllowedRoomBfsNode g.toRoomGraph ctx start}
    (hresult : allowedRoomBfsTotalSearch g ctx target state hinv = some node) :
    node.room = target := by
  fun_induction allowedRoomBfsTotalSearch g ctx target state hinv <;> simp_all

theorem allowed_room_bfs_total_sound
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms)
    {node : AllowedRoomBfsNode g.toRoomGraph ctx start}
    (hresult : allowedRoomBfsTotal g ctx start target hstart = some node) :
    node.room = target ∧ RoomReachable g.toRoomGraph start target ∧
      RouteAllowed ctx start node.route.hops := by
  have htarget : node.room = target := by
    apply allowedRoomBfsTotalSearch_returns_target g ctx target _ _ hresult
  exact ⟨htarget, ⟨htarget ▸ node.route⟩, node.allowed⟩

theorem allowedRoomBfsTotalSearch_le_allowed_route
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (target : RoomCoord)
    {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (hinv : AllowedStateInvariant g ctx state)
    (route : RoomRoute g.toRoomGraph start target)
    (hallowed : RouteAllowed ctx start route.hops)
    (witness : AllowedRoomBfsNode g.toRoomGraph ctx start)
    (hwitness : witness ∈ state.processed ++ state.queue)
    (hwitnessRoom : witness.room = start)
    (hwitnessLen : witness.route.hops.length = 0)
    (hordered : AllowedQueueBreadthOrdered state.queue)
    (hhistory : AllowedHistoryCoverage state)
    (hprocessedLe : AllowedProcessedLeQueue state)
    (hedgeBound : AllowedProcessedEdgeBound g ctx state)
    (htargetNotProcessed : AllowedTargetNotProcessed target state)
    {result : AllowedRoomBfsNode g.toRoomGraph ctx start}
    (hresult : allowedRoomBfsTotalSearch g ctx target state hinv = some result) :
    result.route.hops.length ≤ route.hops.length := by
  fun_induction allowedRoomBfsTotalSearch g ctx target state hinv
  · simp_all
  · rename_i state hinv head rest hqueue heq
    simp at hresult
    subst result
    have hb := allowed_queue_head_le_route_from_history g ctx state head rest hqueue
      hordered hedgeBound htargetNotProcessed start route.hops 0 witness
      route.valid hallowed route.endsAt hwitness hwitnessRoom (by omega)
    simpa using hb
  · rename_i state hinv head rest hqueue hne added next ih
    have hinvHead : AllowedStateInvariant g ctx
        { queue := head :: rest, seen := state.seen,
          processed := state.processed } := by
      simpa [AllowedStateInvariant, hqueue] using hinv
    have horderedHead : AllowedQueueBreadthOrdered (head :: rest) := by
      simpa [hqueue] using hordered
    have horderedNext : AllowedQueueBreadthOrdered next.queue := by
      simpa [next, added] using
        allowedQueueBreadthOrdered_step g ctx head rest state.seen horderedHead
    have hprocessedLeNext : AllowedProcessedLeQueue next := by
      simpa [next, added] using allowedProcessedLeQueue_step
        g ctx state head rest hqueue hprocessedLe hordered
    have hhistoryNext : AllowedHistoryCoverage next := by
      simpa [next, added] using
        allowedHistoryCoverage_step g ctx state head rest hqueue hhistory
    have hedgeBoundNext : AllowedProcessedEdgeBound g ctx next := by
      simpa [next, added] using allowedProcessedEdgeBound_step
        g ctx state head rest hqueue hedgeBound hhistory hprocessedLe hordered
    have htargetNext : AllowedTargetNotProcessed target next := by
      simpa [next, added] using allowedTargetNotProcessed_step
        g ctx target state head rest hqueue hne htargetNotProcessed
    have hwitnessNext : witness ∈ next.processed ++ next.queue := by
      simpa [next, added] using
        allowedHistoryMember_step g ctx state head rest hqueue witness hwitness
    exact ih hwitnessNext horderedNext hhistoryNext hprocessedLeNext
      hedgeBoundNext htargetNext hresult

theorem allowed_room_bfs_total_shortest
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms)
    {result : AllowedRoomBfsNode g.toRoomGraph ctx start}
    (hresult : allowedRoomBfsTotal g ctx start target hstart = some result) :
    ∀ route : RoomRoute g.toRoomGraph start target,
      RouteAllowed ctx start route.hops →
      result.route.hops.length ≤ route.hops.length := by
  intro route hallowed
  let initialNode := emptyAllowedRoomBfsNode g.toRoomGraph ctx start
  let initialState : AllowedRoomBfsState g.toRoomGraph ctx start :=
    { queue := [initialNode], seen := [start] }
  apply allowedRoomBfsTotalSearch_le_allowed_route
    g ctx target initialState
    (allowedStateInvariant_initial g ctx start hstart)
    route hallowed initialNode
  · simp [initialState, initialNode]
  · rfl
  · rfl
  · simpa [initialState, initialNode] using
      allowedQueueBreadthOrdered_initial g.toRoomGraph ctx start
  · simpa [initialState, initialNode] using
      allowedHistoryCoverage_initial g ctx start
  · simpa [initialState, initialNode] using
      allowedProcessedLeQueue_initial g ctx start
  · simpa [initialState, initialNode] using
      allowedProcessedEdgeBound_initial g ctx start
  · simpa [initialState, initialNode] using
      allowedTargetNotProcessed_initial g ctx start target
  · exact hresult

theorem allowedRoomBfsTotalSearch_complete
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (target : RoomCoord)
    {start : RoomCoord}
    (state : AllowedRoomBfsState g.toRoomGraph ctx start)
    (hinv : AllowedStateInvariant g ctx state)
    (route : RoomRoute g.toRoomGraph start target)
    (hallowed : RouteAllowed ctx start route.hops)
    (hstartSeen : start ∈ state.seen)
    (hdiscovery : AllowedDiscoveryInvariant g ctx state.seen state.queue)
    (htargetQueued : AllowedTargetQueued target state.seen state.queue) :
    ∃ node, allowedRoomBfsTotalSearch g ctx target state hinv = some node := by
  fun_induction allowedRoomBfsTotalSearch g ctx target state hinv
  · rename_i state hinv hqueue
    have hclosed : ∀ room ∈ state.seen, AllowedExpanded g ctx state.seen room := by
      intro room hroom
      rcases hdiscovery room hroom with hexp | hqueued
      · exact hexp
      · rcases hqueued with ⟨node, hnode, _⟩
        rw [hqueue] at hnode
        exact (List.not_mem_nil hnode).elim
    have htargetSeen := allowed_route_target_mem_of_closed g ctx route hallowed
      state.seen hstartSeen hclosed
    rcases htargetQueued htargetSeen with ⟨node, hnode, _⟩
    rw [hqueue] at hnode
    exact (List.not_mem_nil hnode).elim
  · rename_i state hinv head rest hqueue heq
    exact ⟨head, rfl⟩
  · rename_i state hinv head rest hqueue hne added next ih
    have hinvHead : AllowedStateInvariant g ctx
        { queue := head :: rest, seen := state.seen } := by
      simpa [AllowedStateInvariant, hqueue] using hinv
    have hinvNext := allowedStateInvariant_step g ctx head rest state.seen hinvHead
    have hstartNext : start ∈ added.2 :=
      enqueueAllowedFresh_seen_monotone _ state.seen start hstartSeen
    have hdiscHead : AllowedDiscoveryInvariant g ctx state.seen (head :: rest) := by
      simpa [hqueue] using hdiscovery
    have hdiscNext := allowedDiscoveryInvariant_step g ctx head rest state.seen hdiscHead
    have htqHead : AllowedTargetQueued target state.seen (head :: rest) := by
      simpa [hqueue] using htargetQueued
    have htqNext := allowedTargetQueued_step g ctx target head rest state.seen hne htqHead
    obtain ⟨node, hnode⟩ := ih hstartNext hdiscNext htqNext
    exact ⟨node, by simpa [hqueue, hne, added, next] using hnode⟩

theorem allowed_room_bfs_total_complete
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms)
    (hreachable : AllowedRoomReachable g.toRoomGraph ctx start target) :
    ∃ node, allowedRoomBfsTotal g ctx start target hstart = some node := by
  rcases hreachable with ⟨route, hallowed⟩
  apply allowedRoomBfsTotalSearch_complete g ctx target
    { queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start], seen := [start] }
    (allowedStateInvariant_initial g ctx start hstart)
    route hallowed
  · simp
  · exact allowedDiscoveryInvariant_initial g ctx start
  · exact allowedTargetQueued_initial g ctx start target

theorem allowed_room_bfs_total_none_unreachable
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms)
    (hnone : allowedRoomBfsTotal g ctx start target hstart = none) :
    ¬ AllowedRoomReachable g.toRoomGraph ctx start target := by
  intro hreachable
  obtain ⟨node, hsome⟩ :=
    allowed_room_bfs_total_complete g ctx start target hstart hreachable
  rw [hnone] at hsome
  contradiction

theorem allowed_fifo_total_first_hop_sound
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms)
    {result : AllowedRoomBfsNode g.toRoomGraph ctx start} {dir : Direction}
    (hresult : allowedRoomBfsTotal g ctx start target hstart = some result)
    (hhop : firstHopOfRoute result.route = some dir) :
    ∃ next, g.edge start dir next ∧
      AllowedRoomReachable g.toRoomGraph ctx start target := by
  obtain ⟨next, hedge⟩ := first_hop_sound result.route hhop
  have hsound := allowed_room_bfs_total_sound g ctx start target hstart hresult
  rcases hsound with ⟨rfl, _⟩
  exact ⟨next, hedge, ⟨result.route, result.allowed⟩⟩

theorem allowed_fifo_total_first_hop_complete
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms)
    (hne : start ≠ target)
    (hreachable : AllowedRoomReachable g.toRoomGraph ctx start target) :
    ∃ result dir,
      allowedRoomBfsTotal g ctx start target hstart = some result ∧
      firstHopOfRoute result.route = some dir := by
  obtain ⟨result, hresult⟩ :=
    allowed_room_bfs_total_complete g ctx start target hstart hreachable
  have htarget := (allowed_room_bfs_total_sound
    g ctx start target hstart hresult).1
  have hneResult : start ≠ result.room := by
    intro heq
    exact hne (heq.trans htarget)
  obtain ⟨dir, hdir⟩ := first_hop_complete_of_route result.route hneResult
  exact ⟨result, dir, hresult, hdir⟩

def allowedRoomBfsSearch (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (target : RoomCoord) : Nat → {start : RoomCoord} →
      AllowedRoomBfsState g.toRoomGraph ctx start →
      Option (AllowedRoomBfsNode g.toRoomGraph ctx start)
  | 0, _, _ => none
  | fuel + 1, _, state =>
      match state.queue with
      | [] => none
      | node :: rest =>
          if node.room = target then some node
          else
            let added := enqueueAllowedFresh
              (expandAllowedRoomNode g ctx node) state.seen
            allowedRoomBfsSearch g ctx target fuel
              { queue := rest ++ added.1, seen := added.2 }

def allowedRoomBfs (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (fuel : Nat) (start target : RoomCoord) :
    Option (AllowedRoomBfsNode g.toRoomGraph ctx start) :=
  allowedRoomBfsSearch g ctx target fuel {
    queue := [emptyAllowedRoomBfsNode g.toRoomGraph ctx start]
    seen := [start]
  }

theorem allowedRoomBfsSearch_returns_target
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (target : RoomCoord) :
    ∀ fuel {start : RoomCoord}
      (state : AllowedRoomBfsState g.toRoomGraph ctx start)
      {node : AllowedRoomBfsNode g.toRoomGraph ctx start},
      allowedRoomBfsSearch g ctx target fuel state = some node →
      node.room = target := by
  intro fuel
  induction fuel with
  | zero => intro start state node h; simp [allowedRoomBfsSearch] at h
  | succ fuel ih =>
      intro start state node h
      cases hqueue : state.queue with
      | nil => simp [allowedRoomBfsSearch, hqueue] at h
      | cons head rest =>
          simp only [allowedRoomBfsSearch, hqueue] at h
          split at h
          · rename_i heq
            cases h
            exact heq
          · exact ih _ h

theorem allowed_room_bfs_sound
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (fuel : Nat)
    (start target : RoomCoord)
    {node : AllowedRoomBfsNode g.toRoomGraph ctx start}
    (hresult : allowedRoomBfs g ctx fuel start target = some node) :
    node.room = target ∧ RoomReachable g.toRoomGraph start target ∧
      RouteAllowed ctx start node.route.hops := by
  have htarget : node.room = target := by
    apply allowedRoomBfsSearch_returns_target g ctx target fuel
    exact hresult
  exact ⟨htarget, ⟨htarget ▸ node.route⟩, node.allowed⟩

theorem routeAllowed_first_hop
    {ctx : RoomRoutingContext} {g : RoomGraph} {start target : RoomCoord}
    (route : RoomRoute g start target) (hallowed : RouteAllowed ctx start route.hops)
    {dir : Direction} (hhop : firstHopOfRoute route = some dir) :
    roomEdgeAllowed ctx start dir = true := by
  cases h : route.hops with
  | nil => simp [firstHopOfRoute, h] at hhop
  | cons hop rest =>
      rcases hop with ⟨firstDir, next⟩
      simp [firstHopOfRoute, h] at hhop
      subst firstDir
      simp only [h, RouteAllowed] at hallowed
      exact hallowed.1

theorem allowed_fifo_total_respects_locked_exit
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms)
    {result : AllowedRoomBfsNode g.toRoomGraph ctx start} {dir : Direction}
    (_hresult : allowedRoomBfsTotal g ctx start target hstart = some result)
    (hhop : firstHopOfRoute result.route = some dir)
    (hlocked : ctx.locked start dir = true)
    (hkeys : ctx.keys = 0)
    (hunvisited : ctx.visitedExit start dir = false) : False := by
  have hallowed := routeAllowed_first_hop result.route result.allowed hhop
  rw [roomEdgeAllowed_locked_no_key_unvisited ctx start dir
    hlocked hkeys hunvisited] at hallowed
  contradiction

theorem allowed_fifo_respects_locked_exit
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext) (fuel : Nat)
    (start target : RoomCoord)
    {node : AllowedRoomBfsNode g.toRoomGraph ctx start} {dir : Direction}
    (_hresult : allowedRoomBfs g ctx fuel start target = some node)
    (hhop : firstHopOfRoute node.route = some dir)
    (hlocked : ctx.locked start dir = true)
    (hkeys : ctx.keys = 0)
    (hunvisited : ctx.visitedExit start dir = false) : False := by
  have hallowed := routeAllowed_first_hop node.route node.allowed hhop
  rw [roomEdgeAllowed_locked_no_key_unvisited ctx start dir
    hlocked hkeys hunvisited] at hallowed
  contradiction

theorem validRoomHops_rooms
    (g : FiniteRoomGraph) : ∀ {start : RoomCoord} {hops : List RoomHop},
    ValidRoomHops g.toRoomGraph start hops →
    hops ≠ [] → start ∈ g.rooms := by
  intro start hops hvalid hne
  cases hops with
  | nil => contradiction
  | cons hop rest =>
      rcases hop with ⟨dir, next⟩
      exact (g.edge_rooms start dir next hvalid.1).1

theorem validRoomHops_append
    {g : RoomGraph} {start current next : RoomCoord}
    {hops : List RoomHop} (hvalid : ValidRoomHops g start hops)
    (hend : routeEnd start hops = current) {dir : Direction}
    (hedge : g.edge current dir next) :
    ValidRoomHops g start (hops ++ [(dir, next)]) := by
  induction hops generalizing start current next dir with
  | nil =>
      simp [routeEnd] at hend
      subst current
      simpa [ValidRoomHops] using hedge
  | cons hop rest ih =>
      rcases hop with ⟨firstDir, firstNext⟩
      simp only [ValidRoomHops] at hvalid
      simp only [routeEnd] at hend
      simp only [List.cons_append, ValidRoomHops]
      exact ⟨hvalid.1, ih hvalid.2 hend hedge⟩

theorem routeEnd_append_hop
    (start current next : RoomCoord) (hops : List RoomHop)
    (hend : routeEnd start hops = current) (dir : Direction) :
    routeEnd start (hops ++ [(dir, next)]) = next := by
  induction hops generalizing start with
  | nil => simp [routeEnd]
  | cons hop rest ih =>
      rcases hop with ⟨d, n⟩
      simp only [routeEnd] at hend
      simp only [List.cons_append, routeEnd]
      exact ih n hend

def RoomRoute.extend {g : RoomGraph} {start current : RoomCoord}
    (route : RoomRoute g start current) (neighbor : CertifiedNeighbor g current) :
    RoomRoute g start neighbor.next where
  hops := route.hops ++ [(neighbor.dir, neighbor.next)]
  valid := validRoomHops_append route.valid route.endsAt neighbor.edge_ok
  endsAt := routeEnd_append_hop start current neighbor.next route.hops
    route.endsAt neighbor.dir

@[simp] theorem RoomRoute.extend_length
    {g : RoomGraph} {start current : RoomCoord}
    (route : RoomRoute g start current) (neighbor : CertifiedNeighbor g current) :
    (route.extend neighbor).hops.length = route.hops.length + 1 := by
  simp [RoomRoute.extend]

def emptyRoomRoute (g : RoomGraph) (start : RoomCoord) : RoomRoute g start start where
  hops := []
  valid := by simp [ValidRoomHops]
  endsAt := by simp [routeEnd]

structure RoomBfsNode (g : RoomGraph) (start : RoomCoord) where
  room : RoomCoord
  route : RoomRoute g start room

def expandRoomNode (g : FiniteRoomGraph) {start : RoomCoord}
    (node : RoomBfsNode g.toRoomGraph start) :
    List (RoomBfsNode g.toRoomGraph start) :=
  (g.neighbors node.room).map fun neighbor =>
    { room := neighbor.next, route := node.route.extend neighbor }

theorem expandRoomNode_member
    (g : FiniteRoomGraph) {start : RoomCoord}
    (node child : RoomBfsNode g.toRoomGraph start)
    (hmem : child ∈ expandRoomNode g node) :
    ∃ neighbor ∈ g.neighbors node.room,
      child.room = neighbor.next ∧
      child.route.hops = node.route.hops ++ [(neighbor.dir, neighbor.next)] ∧
      g.edge node.room neighbor.dir neighbor.next := by
  unfold expandRoomNode at hmem
  rw [List.mem_map] at hmem
  obtain ⟨neighbor, hneighbor, rfl⟩ := hmem
  exact ⟨neighbor, hneighbor, rfl, rfl, neighbor.edge_ok⟩

theorem expandRoomNode_depth
    (g : FiniteRoomGraph) {start : RoomCoord}
    (node child : RoomBfsNode g.toRoomGraph start)
    (hmem : child ∈ expandRoomNode g node) :
    child.route.hops.length = node.route.hops.length + 1 := by
  obtain ⟨neighbor, _, _, hroute, _⟩ := expandRoomNode_member g node child hmem
  rw [hroute]
  simp

/-- Fuel-bounded FIFO room search.  Children are appended at the end, matching
the queue discipline of Python's `_first_hop`. -/
def roomBfsSearch (g : FiniteRoomGraph) (target : RoomCoord) :
    Nat → {start : RoomCoord} → List (RoomBfsNode g.toRoomGraph start) →
      Option (RoomBfsNode g.toRoomGraph start)
  | 0, _, _ => none
  | fuel + 1, _, queue =>
      match queue with
      | [] => none
      | node :: rest =>
          if node.room = target then some node
          else roomBfsSearch g target fuel (rest ++ expandRoomNode g node)

def roomBfs (g : FiniteRoomGraph) (fuel : Nat)
    (start target : RoomCoord) : Option (RoomBfsNode g.toRoomGraph start) :=
  roomBfsSearch g target fuel
    [{ room := start, route := emptyRoomRoute g.toRoomGraph start }]

/-- The dependent return type certifies that every returned BFS route starts at
the requested room and every hop is a graph edge. -/
theorem room_bfs_route_sound (g : FiniteRoomGraph) (fuel : Nat)
    (start target : RoomCoord) {node : RoomBfsNode g.toRoomGraph start}
    (_hresult : roomBfs g fuel start target = some node) :
    ValidRoomHops g.toRoomGraph start node.route.hops ∧
      routeEnd start node.route.hops = node.room := by
  exact ⟨node.route.valid, node.route.endsAt⟩

theorem roomBfsSearch_returns_target (g : FiniteRoomGraph) (target : RoomCoord) :
    ∀ fuel {start : RoomCoord} (queue : List (RoomBfsNode g.toRoomGraph start))
      {node : RoomBfsNode g.toRoomGraph start},
      roomBfsSearch g target fuel queue = some node → node.room = target := by
  intro fuel
  induction fuel with
  | zero => intro start queue node h; simp [roomBfsSearch] at h
  | succ fuel ih =>
      intro start queue node h
      cases queue with
      | nil => simp [roomBfsSearch] at h
      | cons head rest =>
          simp only [roomBfsSearch] at h
          split at h
          · next heq =>
              cases h
              exact heq
          · exact ih _ h

theorem room_bfs_reaches_target (g : FiniteRoomGraph) (fuel : Nat)
    (start target : RoomCoord) {node : RoomBfsNode g.toRoomGraph start}
    (hresult : roomBfs g fuel start target = some node) :
    node.room = target ∧ RoomReachable g.toRoomGraph start target := by
  have htarget : node.room = target := by
    apply roomBfsSearch_returns_target g target fuel
    exact hresult
  constructor
  · exact htarget
  · exact ⟨htarget ▸ node.route⟩

theorem room_bfs_start_eq_target (g : FiniteRoomGraph) (fuel : Nat)
    (start : RoomCoord) :
    (roomBfs g (fuel + 1) start start).map RoomBfsNode.room = some start := by
  simp [roomBfs, roomBfsSearch]

theorem room_bfs_success_has_first_hop (g : FiniteRoomGraph) (fuel : Nat)
    (start target : RoomCoord) (hne : start ≠ target)
    {node : RoomBfsNode g.toRoomGraph start}
    (hresult : roomBfs g fuel start target = some node) :
    ∃ dir, firstHopOfRoute node.route = some dir := by
  have htarget := (room_bfs_reaches_target g fuel start target hresult).1
  apply first_hop_complete_of_route node.route
  simpa [htarget] using hne

/-- Once the executable search result is known to be shortest, its first hop
belongs to a minimum-hop route.  The remaining hard theorem is that FIFO+seen
establishes the `RouteShortest` premise automatically. -/
theorem executable_first_hop_shortest
    (g : FiniteRoomGraph) (fuel : Nat) (start target : RoomCoord)
    {node : RoomBfsNode g.toRoomGraph start}
    (hresult : roomBfs g fuel start target = some node)
    (hshort : RouteShortest g.toRoomGraph node.route) :
    node.room = target ∧
    ∀ other : RoomRoute g.toRoomGraph start node.room,
      node.route.hops.length ≤ other.hops.length := by
  exact ⟨(room_bfs_reaches_target g fuel start target hresult).1,
    route_shortest_length_bound node.route hshort⟩

theorem executable_first_hop_sound (g : FiniteRoomGraph) (fuel : Nat)
    (start target : RoomCoord) {node : RoomBfsNode g.toRoomGraph start}
    {dir : Direction} (hresult : roomBfs g fuel start target = some node)
    (hhop : firstHopOfRoute node.route = some dir) :
    ∃ next, g.edge start dir next ∧ RoomReachable g.toRoomGraph start target := by
  obtain ⟨next, hedge⟩ := first_hop_sound node.route hhop
  exact ⟨next, hedge, (room_bfs_reaches_target g fuel start target hresult).2⟩

/-! ## FIFO search with Python-style `seen` filtering -/

/-- Scan candidate children from left to right.  A room is inserted into
`seen` as soon as it is accepted, exactly like Python's `parent` dictionary. -/
def enqueueFresh {g : RoomGraph} {start : RoomCoord} :
    List (RoomBfsNode g start) → List RoomCoord →
      List (RoomBfsNode g start) × List RoomCoord
  | [], seen => ([], seen)
  | node :: rest, seen =>
      if seen.contains node.room then
        enqueueFresh rest seen
      else
        let result := enqueueFresh rest (node.room :: seen)
        (node :: result.1, result.2)

@[simp] theorem enqueueFresh_nil {g : RoomGraph} {start : RoomCoord}
    (seen : List RoomCoord) :
    enqueueFresh (g := g) (start := start) [] seen = ([], seen) := rfl

theorem enqueueFresh_nodes_subset {g : RoomGraph} {start : RoomCoord} :
    ∀ (candidates : List (RoomBfsNode g start)) (seen : List RoomCoord)
      (node : RoomBfsNode g start),
      node ∈ (enqueueFresh candidates seen).1 → node ∈ candidates := by
  intro candidates
  induction candidates with
  | nil => intro seen node h; simp at h
  | cons head rest ih =>
      intro seen node h
      simp only [enqueueFresh] at h
      split at h
      · exact List.mem_cons_of_mem head (ih seen node h)
      · simp only [List.mem_cons] at h
        cases h with
        | inl heq => simp [heq]
        | inr hmem =>
            exact List.mem_cons_of_mem head
              (ih (head.room :: seen) node hmem)

theorem enqueueFresh_output_not_in_initial_seen
    {g : RoomGraph} {start : RoomCoord} :
    ∀ (candidates : List (RoomBfsNode g start)) (seen : List RoomCoord)
      (node : RoomBfsNode g start),
      node ∈ (enqueueFresh candidates seen).1 → node.room ∉ seen := by
  intro candidates
  induction candidates with
  | nil => intro seen node h; simp at h
  | cons head rest ih =>
      intro seen node h
      simp only [enqueueFresh] at h
      split at h
      · exact ih seen node h
      · rename_i hfresh
        simp only [List.mem_cons] at h
        cases h with
        | inl heq =>
            subst node
            simpa using hfresh
        | inr hmem =>
            have hn := ih (head.room :: seen) node hmem
            exact fun hs => hn (by simp [hs])

theorem enqueueFresh_seen_monotone
    {g : RoomGraph} {start : RoomCoord} :
    ∀ (candidates : List (RoomBfsNode g start)) (seen : List RoomCoord)
      (room : RoomCoord),
      room ∈ seen → room ∈ (enqueueFresh candidates seen).2 := by
  intro candidates
  induction candidates with
  | nil => intro seen room h; exact h
  | cons head rest ih =>
      intro seen room h
      simp only [enqueueFresh]
      split
      · exact ih seen room h
      · exact ih (head.room :: seen) room (by simp [h])

theorem enqueueFresh_output_registered
    {g : RoomGraph} {start : RoomCoord} :
    ∀ (candidates : List (RoomBfsNode g start)) (seen : List RoomCoord)
      (node : RoomBfsNode g start),
      node ∈ (enqueueFresh candidates seen).1 →
      node.room ∈ (enqueueFresh candidates seen).2 := by
  intro candidates
  induction candidates with
  | nil => intro seen node h; simp at h
  | cons head rest ih =>
      intro seen node h
      by_cases hfresh : head.room ∈ seen
      · simp [enqueueFresh, hfresh] at h ⊢
        exact ih seen node h
      · simp [enqueueFresh, hfresh] at h ⊢
        cases h with
        | inl heq =>
            subst node
            exact enqueueFresh_seen_monotone rest (head.room :: seen)
              head.room (by simp)
        | inr hmem => exact ih (head.room :: seen) node hmem

theorem enqueueFresh_seen_nodup
    {g : RoomGraph} {start : RoomCoord} :
    ∀ (candidates : List (RoomBfsNode g start)) (seen : List RoomCoord),
      seen.Nodup → (enqueueFresh candidates seen).2.Nodup := by
  intro candidates
  induction candidates with
  | nil => intro seen h; exact h
  | cons head rest ih =>
      intro seen hseen
      simp only [enqueueFresh]
      split
      · exact ih seen hseen
      · rename_i hfresh
        apply ih (head.room :: seen)
        exact List.nodup_cons.mpr ⟨by simpa using hfresh, hseen⟩

theorem enqueueFresh_seen_subset_rooms
    (g : FiniteRoomGraph) {start : RoomCoord} :
    ∀ (candidates : List (RoomBfsNode g.toRoomGraph start))
      (seen : List RoomCoord),
      (∀ room ∈ seen, room ∈ g.rooms) →
      (∀ node ∈ candidates, node.room ∈ g.rooms) →
      ∀ room ∈ (enqueueFresh candidates seen).2, room ∈ g.rooms := by
  intro candidates
  induction candidates with
  | nil => intro seen hseen _ room hroom; exact hseen room hroom
  | cons head rest ih =>
      intro seen hseen hcandidates
      simp only [enqueueFresh]
      split
      · apply ih seen hseen
        intro node hnode
        exact hcandidates node (by simp [hnode])
      · apply ih (head.room :: seen)
        · intro room hroom
          simp only [List.mem_cons] at hroom
          cases hroom with
          | inl heq => simpa [← heq] using hcandidates head (by simp)
          | inr hmem => exact hseen room hmem
        · intro node hnode
          exact hcandidates node (by simp [hnode])

def NodesAtDepth {g : RoomGraph} {start : RoomCoord}
    (nodes : List (RoomBfsNode g start)) (depth : Nat) : Prop :=
  ∀ node ∈ nodes, node.route.hops.length = depth

theorem enqueueFresh_preserves_depth
    {g : RoomGraph} {start : RoomCoord}
    (candidates : List (RoomBfsNode g start)) (seen : List RoomCoord)
    (depth : Nat) (hdepth : NodesAtDepth candidates depth) :
    NodesAtDepth (enqueueFresh candidates seen).1 depth := by
  intro node hnode
  exact hdepth node (enqueueFresh_nodes_subset candidates seen node hnode)

theorem expandRoomNode_at_next_depth
    (g : FiniteRoomGraph) {start : RoomCoord}
    (node : RoomBfsNode g.toRoomGraph start) :
    NodesAtDepth (expandRoomNode g node) (node.route.hops.length + 1) := by
  intro child hchild
  exact expandRoomNode_depth g node child hchild

theorem enqueue_expansion_at_next_depth
    (g : FiniteRoomGraph) {start : RoomCoord}
    (node : RoomBfsNode g.toRoomGraph start) (seen : List RoomCoord) :
    NodesAtDepth (enqueueFresh (expandRoomNode g node) seen).1
      (node.route.hops.length + 1) := by
  exact enqueueFresh_preserves_depth _ _ _ (expandRoomNode_at_next_depth g node)

structure RoomBfsState (g : RoomGraph) (start : RoomCoord) where
  queue : List (RoomBfsNode g start)
  seen : List RoomCoord

def roomBfsSeenSearch (g : FiniteRoomGraph) (target : RoomCoord) :
    Nat → {start : RoomCoord} → RoomBfsState g.toRoomGraph start →
      Option (RoomBfsNode g.toRoomGraph start)
  | 0, _, _ => none
  | fuel + 1, _, state =>
      match state.queue with
      | [] => none
      | node :: rest =>
          if node.room = target then some node
          else
            let added := enqueueFresh (expandRoomNode g node) state.seen
            roomBfsSeenSearch g target fuel
              { queue := rest ++ added.1, seen := added.2 }

def roomBfsSeen (g : FiniteRoomGraph) (fuel : Nat)
    (start target : RoomCoord) : Option (RoomBfsNode g.toRoomGraph start) :=
  roomBfsSeenSearch g target fuel {
    queue := [{ room := start, route := emptyRoomRoute g.toRoomGraph start }]
    seen := [start]
  }

theorem roomBfsSeenSearch_returns_target
    (g : FiniteRoomGraph) (target : RoomCoord) :
    ∀ fuel {start : RoomCoord} (state : RoomBfsState g.toRoomGraph start)
      {node : RoomBfsNode g.toRoomGraph start},
      roomBfsSeenSearch g target fuel state = some node → node.room = target := by
  intro fuel
  induction fuel with
  | zero => intro start state node h; simp [roomBfsSeenSearch] at h
  | succ fuel ih =>
      intro start state node h
      cases hqueue : state.queue with
      | nil => simp [roomBfsSeenSearch, hqueue] at h
      | cons head rest =>
          simp only [roomBfsSeenSearch, hqueue] at h
          split at h
          · rename_i heq
            cases h
            exact heq
          · exact ih _ h

theorem room_bfs_seen_reaches_target
    (g : FiniteRoomGraph) (fuel : Nat) (start target : RoomCoord)
    {node : RoomBfsNode g.toRoomGraph start}
    (hresult : roomBfsSeen g fuel start target = some node) :
    node.room = target ∧ RoomReachable g.toRoomGraph start target := by
  have htarget : node.room = target := by
    apply roomBfsSeenSearch_returns_target g target fuel
    exact hresult
  exact ⟨htarget, ⟨htarget ▸ node.route⟩⟩

theorem room_bfs_seen_success_has_first_hop
    (g : FiniteRoomGraph) (fuel : Nat) (start target : RoomCoord)
    (hne : start ≠ target) {node : RoomBfsNode g.toRoomGraph start}
    (hresult : roomBfsSeen g fuel start target = some node) :
    ∃ dir, firstHopOfRoute node.route = some dir := by
  apply first_hop_complete_of_route node.route
  simpa [(room_bfs_seen_reaches_target g fuel start target hresult).1] using hne

/-! ## Counterexample for lock filtering not yet represented by the search -/

def counterStart : RoomCoord := (0, 0)
def counterTarget : RoomCoord := (1, 0)

/-- This executable graph exposes the same edge through its neighbor list. -/
def lockedNeighborGraph : FiniteRoomGraph where
  edge room dir next :=
    room = counterStart ∧ dir = .right ∧ next = counterTarget
  rooms := [counterStart, counterTarget]
  rooms_nodup := by native_decide
  neighbors room :=
    if h : room = counterStart then
      [{ dir := .right, next := counterTarget,
         edge_ok := ⟨h, rfl, rfl⟩ }]
    else []
  neighbors_complete room dir next hedge := by
    rcases hedge with ⟨hroom, hdir, hnext⟩
    subst room
    subst dir
    subst next
    refine ⟨{
      dir := .right
      next := counterTarget
      edge_ok := by simp [counterStart, counterTarget]
    }, ?_, rfl, rfl⟩
    simp
  edge_rooms room dir next hedge := by
    rcases hedge with ⟨rfl, rfl, rfl⟩
    constructor <;> simp

def everyExitLocked (_g : RoomGraph) (_room : RoomCoord) (_dir : Direction) : Prop :=
  True

/-- Counterexample to an unconditional locked-exit theorem: the present
`roomBfs` has no routing context or lock filter, so it selects the locked edge. -/
theorem room_bfs_locked_exit_counterexample :
    (roomBfs lockedNeighborGraph 2 counterStart counterTarget).map
        (fun node => (node.room, firstHopOfRoute node.route)) =
      some (counterTarget, some .right) ∧
    everyExitLocked lockedNeighborGraph.toRoomGraph counterStart .right := by
  constructor
  · native_decide
  · trivial

end EnvFormalization
