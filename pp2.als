sig Player {
    role: Role,
    team: Team,
    rank: lone Rank
}

fact oneRolePerPlayer {
    all p: Player |
        one r: Role | p.role = r
}

fact onePlayerPerRolePerTeam {
    all t: Team, r: Role |
        #(t.role & r) = 1
}

fact bannedChampionCannotBeSelected {
    all c: Champion, p: Player |
        c in p.bannedChampions => c not in p.selectedChampions
}

fact oneChampionPerPlayer {
    all p: Player |
        #(p.selectedChampions) = 1
}
