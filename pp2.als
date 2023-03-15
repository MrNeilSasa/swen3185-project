module LeagueofLegends

open util/relation 
open util/ternary

sig Role{} 
sig Top extends Role{}
sig Jungle extends Role{}
sig Mid extends Role{}
sig Bot extends Role{}
sig Support extends Role{}
sig Fill extends Role{}
/*Fill can go in any role in a queue*/
sig Team{
	players: Player
}
sig BlueTeam extends Team{}
sig RedTeam extends Team{}
sig Rank{}
sig RankProgress{}
sig Strike{}
sig DemotionZone extends RankProgress{
	strikes: Strike -> Player
/*A player should not have more than 3 strikes in the DemotionZone */
}
sig NearDemotion extends RankProgress{}
sig Halfway extends RankProgress{}
sig NearPromotion extends RankProgress{}
sig Wins{}
sig Losses{}
sig PromotionZone extends RankProgress{
	wins: Wins -> Player,
	loses: Losses -> Player
	/*Remember the constraints a player should not have more than 2 wins or loses in PromotionZone */
}
enum RankDivisions{Four, Three, Two, One}

sig Iron extends Rank{
	division: RankDivisions	
}
sig Bronze extends Rank{
	division: RankDivisions
}
sig Silver extends Rank{
	division: RankDivisions
}
sig Gold extends Rank{
	division: RankDivisions
}
sig Platinum extends Rank{
	division: RankDivisions
}
sig Diamond extends Rank{
	division: RankDivisions
}
sig Master extends Rank{}
sig Grandmaster extends Rank{}
sig Challenger extends Rank{}
sig SummonersRift{}
sig NormalDraft  extends SummonersRift{}
sig SoloDuo extends SummonersRift{}
sig GameSelection{
	gameSelected:  Player -> one SummonersRift  
} /* GameSelection is the 1st step but no longer a phase */
	/*A player should not be on a team if a game isnt selected and player is InLobby Tristyn */ 

sig Phase{
	gamemode: SummonersRift
}

sig InLobby extends Phase{
	queue: Player -> Queue
	/* InLobby a player should have two roles */
	/*A player should not be on a team while InLobby  Tristyn */   
}  
sig Queue{
	gamemode: SummonersRift,
	players: Player
/*	top: Top    (Player -> Role) where Role == Top
	mid: Mid 
	jg: Jungle
	sup: Sup*/
}

sig Match{
	rank: lone Rank,
	gamemode: SummonersRift,
	players: Player,
	redTeam: RedTeam,
	blueTeam: BlueTeam,
	--Lucas
	/*If the version of the gamemode is SoloDuo then the match must have a rank*/
	/*if the version of the gamemode is NormalDraft the match should not have a rank */ 

}
sig ChampSelect extends Phase{
	redTeam: RedTeam,
	blueTeam: BlueTeam

}
sig Champion{
	role: one Role /*A champion has one role */
	
}

sig BanPhase extends ChampSelect{
	ban: Player -> Champion

}
sig ChampionSelect extends ChampSelect{
	selectedChampion: Player -> Champion
	/*A player can only select one champion */
	/*There are no duplicate champions */
	/*The player selecting the champion must match the champions role */
}
sig Results extends Phase{}
sig Player {
	role: Role,
	team: Team,
	rank: lone Rank,
	rankProgression:  RankProgress,
	phase: Phase
	-- Lucas
    	/* A player must have a rankProgress */
	/* A player can only have one rankProgress */
	/* A player can only be on one team */
}
/* 
•	Players can only be matched with/against others of same Rank for Solo/Duo mode
•	Every player must have a rank.
•	Every player must have a Demotion Status
•	Every player must have a Promotion Status
•	Every player must have Rank Progress
•	Players of all ranks can be match with each other for Draft mode
•	Only one instance of a champion can be chosen in a match. Multiple players cannot choose the same champion in a match regardless of team.
•	All players must select at least one preferred role before entering the matchmaker
•	Each player can ban at most one champion during ban phase.

	/*A player cannot ban the same champion a teammate has banned. i.e. No duplicate bans on the same team */
	/* Bans can be a minimum of 5 champions and a maximum of 10. */
	/* A player must be on a team */
	/* A player can only be on one team */
	/* Players should only have one role in ChampSelect */
/*


•

•	Each team must have 5 members.


•	When a Game Session end their must be a winning team and a losing team

•	In a Solo/Duo Game a win must cause some progression towards the next rank and should be reflected in Rank Progress incrementing by one or in the state of Promos. 
	(This is now a function)
•	In a Solo/Duo Game a loss must cause some regression in your current Rank Progress decrementing by one stage unless the player is in the Demotion Zone
	(This is now a function)
•	A Player must be a Strike3 Demotion Status to demote down a rank. /* Change in abstractions that Demotion and Promotion Statues will notify whether or not a player
	should be demoted or promoted 
•	A Player must obtain two wins in Promos in order to advance to the next rank.
	/*Remember the constraints a player should not have more than 2 wins or loses in PromotionZone 
•	The result of a Draft mode game cannot affect your rank or Ranked Progress. 
•	When players losses their promo their ranked progress must change to Near Promotion
•	Minimum 5 champions that can be banned a maximum 10 champions
•	When a player is demoted their ranked must go down to subdivision 1 of the ranked in which they demoted to and the Ranked Progress must be Near Promotion.
•	A player can only be in one Game session at a time.
•	A player cannot be in a Game session and champ select at the same time.
•	A player cannot be in multiple matches at once. Tristyn
	A player cannot be in multiple queues at once. Tristyn
	A player cannot be in multiple phases at once Tristyn


*/
fact oneRolePerPlayer {
    all p: Player |
        one r: Role | p.role = r
}

/*A player cannot select more than one gamemode 
fact oneGamemode{
	all s: SummonersRift | eq[#(select2[gameSelected]).s, 1]
} */

/*Gamemode selected should be either NormalDraft or SummonersRift */
fact gameModeType{
	all  s: SummonersRift, g: GameSelection, p: Player | g -> p -> s in gameSelected implies s = NormalDraft or s = SoloDuo
} 

/*
fact onePlayerPerRolePerTeam {
    all t: Team, r: Role |
        #(t.role & r) = 1
} */

/*	No player can select a banned champion. */
fact bannedChampionCannotBeSelected {
    all c: Champion, p: Player |
        p->c in select23[ban]  implies p->c not in select23[selectedChampion]
}
/*
fact oneChampionPerPlayer {
    all p: Player |
        #(p.selectedChampion) = 1
}  */

pred selectingGame[p:Player]{
	some GameSelection
	some Player
	gt[#Player,1]
	gt[#gameSelected, 1]
	some SummonersRift
	some NormalDraft
	some SoloDuo

}
run selectingGame for 4 expect 1

