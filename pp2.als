sig Role{} /* check how enum works and if it is suitable for Roles */
sig Team{}
sig BlueTeam extends Team{}
sig RedTeam extends Team{}
sig Rank{}
sig RankProgress{}

sig Iron extends Rank{}
sig Silver extends Rank{}
sig Gold extends Rank{}
sig Platinum extends Rank{}
sig Diamond extends Rank{}
sig Master extends Rank{}
sig Grandmaster extends Rank{}
sig Challenger extends Rank{}
/* Figure out how to do the subdivions with seq */
sig SummonersRift{}
sig NormalDraft  extends SummonersRift{}
sig SoloDuo extends SummonersRift{}
sig GameSelection /* GameSelection is the 1st step and no longer a phase */
sig Phase{
	gamemode: SummonersRift
}

sig InLobby extends Phase{}  
sig Queue{
	type: SummonersRift
}
sig QueueRanked{}
sig Match{}
sig ChampSelect extends Phase{}
sig Champions{}
sig BanPhase extends ChampSelect{}
sig ChampionSelect extends ChampSelect{}
sig Results extends Phase{}
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
