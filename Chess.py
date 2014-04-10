from copy import deepcopy
from operator import itemgetter
import random
import math

#next steps
#deal with king in check

#################################
#           Globals             #
#################################

INIT_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR'
WHITE = 1
BLACK = 0
#define global variables that use square coordinates as names and contain the equivalent long. Also store in a list to iterate over, and also rank and file number associated with each square. Black's back rank is defined to be the 8th ranks, and file a the first file
SQUARES = []
RANK = {}
FILE = {}
for r in range(8,0,-1):
	index = r*8-1
	for f in 'abcdefgh':
		name = '%s%s' % (f,r)
		exec(name + '='+ str(1L << index))
		SQUARES.append(1L << index)
		RANK[1L << index] = r
		FILE[1L << index] = 8*r-index
		index -= 1

#################################
#          Parameters           #
#################################
PIECE_VALUE = {'Q': 9, 'R': 5, 'B': 3, 'N': 3, 'P': 1}

#################################
#        Useful functions       #
#################################

#long to bit string conversion
def bin(s):
	return str(s) if s <= 1 else bin(s >> 1) + str(s&1)

#for a given square convert long into algebraic notation
def algebraic(sq):
	fileset = 'abcdefgh'
	return fileset[FILE[sq]- 1] + str(RANK[sq])

#function to check formatting of fen code
def check_fen(fen):
		#check fen code has the correct format
		#check there are 8 ranks
		ranks = fen.split("/")
		if len(ranks) != 8:
			raise Exception('Incorrect number of ranks in FEN string')
		#check for allowable characters
		for r in ranks:
			for sq in r:
				if ((sq not in '12345678') and (sq not in 'rnbqkpRNBQKP')):
					raise Exception('Incorrect character in FEN string')
		#check that there are only 8 files
		for r in ranks:
			file_count = 0
			for sq in r:
				if sq in 'rnbqkpRNBQKP':
					file_count += 1
				else:
					file_count += int(sq)
			if file_count != 8:
				raise Exception('Incorrect number of files in FEN string')
		return 

#least signicant bit calculation for bitboards
def lsb(bb):
	return bb & -bb

#function to display a bitboard
def display_bb(bb):
		white = 1
		for r in range(8,0,-1):
			print "\n    +---+---+---+---+---+---+---+---+"
			print " ",r, "|",
			for f in range(8,0,-1):
				val = (8L * (r - 1L)) + (f - 1L)
				if ((1 << val) & bb):
					 print '1',"|",
				else:
					if (white):
						print " ","|",
					else:
						print ".","|",
				white ^= 1
			white ^= 1
		print "\n    +---+---+---+---+---+---+---+---+"
		print "      a   b   c   d   e   f   g   h  \n"
		return

#mirror first rank of a bitboard onto the h-file. used to help generate file attacks from rank attacks
def mirror_rank1_to_hfile(occupancy):
	map = {h1:h1, g1:h2, f1:h3, e1:h4, d1:h5, c1:h6, b1:h7, a1:h8}
	mirror_occ = 0
	for index in range(0,8):
		#extract occupied square 
		occ_sq = occupancy & (1 << index)
		#if non-zero get mirror
		if occ_sq > 0:
			mirror_occ_sq = map[occ_sq]
			#add to mirrored occupancy value for first file
			mirror_occ |= mirror_occ_sq
	return mirror_occ

#array of diagonals to loop over when generating diagonal moves
def getdiagonals():
	diag_nw = [[a1],[b1,a2],[c1,b2,a3],[d1,c2,b3,a4],[e1,d2,c3,b4,a5],[f1,e2,d3,c4,b5,a6],[g1,f2,e3,d4,c5,b6,a7],[h1,g2,f3,e4,d5,c6,b7,a8],[h2,g3,f4,e5,d6,c7,b8],[h3,g4,f5,e6,d7,c8],[h4,g5,f6,e7,d8],[h5,g6,f7,e8],[h6,g7,f8],[h7,g8],[h8]]
	diag_ne = [[h1],[g1,h2],[f1,g2,h3],[e1,f2,g3,h4],[d1,e2,f3,g4,h5],[c1,d2,e3,f4,g5,h6],[b1,c2,d3,e4,f5,g6,h7],[a1,b2,c3,d4,e5,f6,g7,h8],[a2,b3,c4,d5,e6,f7,g8],[a3,b4,c5,d6,e7,f8],[a4,b5,c6,d7,e8],[a5,b6,c7,d8],[a6,b7,c8],[a7,b8],[a8]]
	diagonals  = {'NE': diag_ne, 'NW': diag_nw}
	return diagonals

#a map from a square and a north-east or north-west direction key to a bitboard consisting of 1's along the chosen diagonal. Used when generating diagonal moves for sliding pieces
def getmapsqtodiag():
		diagonals = getdiagonals()
		#array of bitboards, one per diagonal
		diags_bb = {'NE': [], 'NW': []}
		for key in ['NE','NW']:
			for diag in diagonals[key]:
				diag_bb = 0
				for sq in diag:
					diag_bb |= sq
				diags_bb[key].append(diag_bb)
		#map from square to diagonal bb
		map_sq_diags_bb = {'NE': {}, 'NW': {}}
		for key in ['NE','NW']:
			for index in range(0,len(diagonals[key])):
				for sq in diagonals[key][index]:
					map_sq_diags_bb[key][sq] = diags_bb[key][index]
		return map_sq_diags_bb
		
#################################
#          Main Classes         #
#################################

class Position:
	def __init__(self,fen):
		#check format of fen code used to initialise the position
		check_fen(fen)
		#array to keep a count of the different type of pieces on the board. This to help speed up the evaluation function
		self.piece_count = {}
		for k in 'PRNBQKprnbqk':
			self.piece_count[k] = 0
		#generate piece bitboards
		self.piece_bb = {}
		ranks = fen.split("/")
		for k in 'PRNBQKprnbqk':
			self.piece_bb[k] = 0
			index = 63
			for r in ranks:
				for sq in r:
					if (sq in '12345678'): 
						#we have a space move the index
						index -= int(sq)
					elif k == sq:
						self.piece_bb[k] |= 1L << index
						index -= 1
						self.piece_count[k] += 1
					else:
						#a different type of piece
						index -= 1
		#generate bitboards for all white, all black pieces and all pieces
		self.piece_bb['w_pieces'] = 0
		self.piece_bb['b_pieces'] = 0
		for k in 'PRNBQK':
			self.piece_bb['w_pieces'] |= self.piece_bb[k] 
		for k in 'prnbqk':
			self.piece_bb['b_pieces'] |= self.piece_bb[k] 
		self.piece_bb['all_pieces'] = self.piece_bb['w_pieces'] | self.piece_bb['b_pieces']
		return
		
	def update(self,move):
		source_sq = move.getsourcesq()
		dest_sq = move.getdestsq()
		promotedto = move.getpromotedto()
		#determine if this is a white or black move
		pieces = 'PRNBQK'
		other_pieces = 'prnbqk'
		piece_type = 'w_pieces'
		other_type = 'b_pieces'
		if (source_sq & self.piece_bb['b_pieces']):
			pieces = 'prnbqk'
			other_pieces = 'PRNBQK'
			piece_type = 'b_pieces'
			other_type = 'w_pieces'
		#check to see if this was a capture
		if (dest_sq & self.piece_bb[other_type]):
			#set captured square to zero
			self.piece_bb[other_type] ^= dest_sq
			#remove piece
			for other_piece in other_pieces:
				if (dest_sq & self.piece_bb[other_piece]):
					self.piece_bb[other_piece] ^= dest_sq
					self.piece_count[other_piece] -= 1
					break
		#update piece bitboard
		for piece in pieces:
			if (source_sq & self.piece_bb[piece]):
				#set source sq to zero
				self.piece_bb[piece] ^= source_sq
				#set destination square to one
				if promotedto == 0:
					self.piece_bb[piece] ^= dest_sq
				else:
					self.piece_bb[promotedto] ^= dest_sq
				break
		#update general white,black and all piece bitboards
		self.piece_bb[piece_type] ^= source_sq
		self.piece_bb[piece_type] ^= dest_sq
		self.piece_bb['all_pieces'] ^= source_sq
		self.piece_bb['all_pieces'] ^= dest_sq
		return
	
	#main position evaluation function
	def evaluate(self):
		#calculate material imbalance
		eval = 0
		for piece in 'PRNBQ':
			eval += PIECE_VALUE[piece]*(self.piece_count[piece] - self.piece_count[piece.lower()])
		return eval
		
	#function to display position, also provides the evaluation value
	def display(self):
		white = 1
		for r in range(8,0,-1):
			print "\n    +---+---+---+---+---+---+---+---+"
			print " ",r, "|",
			for f in range(8,0,-1):
				val = (8L * (r - 1L)) + (f - 1L)
				piece_count = 0
				for k in 'prnbqkPRNBQK':
					if ((1 << val) & self.piece_bb[k]):
					 	print k,"|",
					 	piece_count += 1
				if piece_count == 0:
					if (white):
						print " ","|",
					else:
						print ".","|",
				elif piece_count > 1:
						raise Exception('invalid piece count in position display')
				white ^= 1
			white ^= 1
		print "\n    +---+---+---+---+---+---+---+---+"
		print "      a   b   c   d   e   f   g   h  \n"
		print "Evaluation: " + str(self.evaluate())
		print "\n"
		return

#preprocessed piece moves stored in arrays of bitboards
class PreProcessedMoves:
	def __init__(self):
		self.knight = self.preproc_knightmoves()
		self.king = self.preproc_kingmoves()
		self.whitepawn = self.preproc_whitepawnmoves()
		self.blackpawn = self.preproc_blackpawnmoves()
		self.rankattacks = self.preproc_rankattacks()
		self.fileattacks = self.preproc_fileattacks()
		self.diagattacks = self.preproc_diagattacks()
		return
	
	def preproc_knightmoves(self):
		#generates a bitboard per square indicating allowable knight moves
		knight = {}
		for sq in SQUARES:
			bb = 0
			for i in (17,15,10,6):
				for dest_sq in (sq << i,sq >> i):
					if dest_sq <= a8 and dest_sq >= h1:
						if abs(RANK[dest_sq]- RANK[sq]) <= 2 and abs(FILE[dest_sq] - FILE[sq]) <= 2:
							bb |= dest_sq
			knight[sq] = bb
		return knight
		
	def preproc_kingmoves(self):
		king = {}
		for sq in SQUARES:
			bb = 0
			for i in (1,7,8,9):
				for dest_sq in (sq << i,sq >> i):
					if dest_sq <= a8 and dest_sq >= h1:
						if abs(RANK[dest_sq]- RANK[sq]) <= 1 and abs(FILE[dest_sq] - FILE[sq]) <= 1:
							bb |= dest_sq
			king[sq] = bb
		return king
		
	def preproc_whitepawnmoves(self):
		#left out capturing moves to be checked for in move generator
		pawn = {}
		#treat enpassant as special case in move generator.
		for sq in SQUARES:
			sq_rank = RANK[sq]
			if sq_rank == 2:
				#in this case can move one or two ranks
				pawn[sq] = sq << 8 | sq << 16
			elif sq_rank == 1 or sq_rank == 8:
				#never have a pawn on first or last rank. in latter case would have been promoted to a different piece
				pawn[sq] = 0
			else:
				#otherwise can move forward one rank
				pawn[sq] = sq << 8
		return pawn
	
	def preproc_blackpawnmoves(self):
		#left out capturing moves to be checked for in move generator
		pawn = {}
		#treat enpassant as special case in move generator.
		for sq in SQUARES:
			sq_rank = RANK[sq]
			if sq_rank == 7:
				#in this case can move one or two ranks
				pawn[sq] = sq >> 8 | sq >> 16
			elif sq_rank == 1 or sq_rank == 8:
				#never have a pawn on first or last rank. in latter case would have been promoted to a different piece
				pawn[sq] = 0
			else:
				#otherwise can move forward one rank
				pawn[sq] = sq >> 8
		return pawn
		
	def preproc_rankattacks(self):
		rank_attacks = {}
		for sq in SQUARES:
			rank_attacks[sq] = {}
		#deal with first rank first
		first_rank = [a1,b1,c1,d1,e1,f1,g1,h1]
		for sq in first_rank:
			#loop over all possible occupancy variations of first rank
			#this will lead to duplicate entries in hash table but occupancy of a
			#rank will be quick to compute in move generation phase (as opposed to the left and right blockers individually)
			for occupancy in range(1,256):
				#look for first left blocker
				left_block_file = 1
				for left in range(FILE[sq]-1,0,-1):
					if ((1 << (8-left)) & occupancy) != 0:
						left_block_file = left
						break
				right_block_file = 8
				for right in range(FILE[sq]+1,9):
					if ((1 << (8-right)) & occupancy) != 0:
						right_block_file = right
						break
				#calculate possible moves
				bb_attacks = 0
				for i in range(left_block_file, FILE[sq]):
					bb_attacks += pow(2,8-i)
				for i in range(FILE[sq]+1, right_block_file+1):
					bb_attacks += pow(2,8-i)			
				#add to hash table
				rank_attacks[sq][occupancy] = bb_attacks
				#calculate attacks for other ranks
				for rank in range(2,9):
					rank_attacks[sq << 8*(rank-1)][occupancy << 8*(rank-1)] = bb_attacks << 8*(rank-1)
		return rank_attacks
		
	def preproc_fileattacks(self):
		#this function assumes rankattacks has already been calculated
		file_attacks = {}
		for sq in SQUARES:
			file_attacks[sq] = {}
	  #deal with first file by rotating first rank rankattacks by 90 degrees
		first_rank = [h1,g1,f1,e1,d1,c1,b1,a1]
		first_file = [h1,h2,h3,h4,h5,h6,h7,h8]
		for occupancy in range(1,256):
			mirror_occ = mirror_rank1_to_hfile(occupancy)
			for index in range(0,8):
				mirror_value = mirror_rank1_to_hfile(self.rankattacks[first_rank[index]][occupancy])
				file_attacks[first_file[index]][mirror_occ] = mirror_value
				#copy accross to other files
				for file in range(2,9):
					file_attacks[first_file[index] << (file -1)][mirror_occ << (file - 1)] = mirror_value << (file - 1) 
		return file_attacks
	
	def preproc_diagattacks(self): 
		diagonals = getdiagonals()
		#first generate attacks along diagonals
		diag_attacks = {'NE':{},'NW':{}}
 		for sq in SQUARES:
				diag_attacks['NE'][sq] = {}
				diag_attacks['NW'][sq] = {}
		#loop over diagonals
		for key in ['NE','NW']:
			for diag in diagonals[key]:
				#loop over squares along diagonal
				sq_index = 0
				for sq in diag:
					#generate occupancy values
					for occ in range(1,pow(2,len(diag))):
						#determine bitboard for occupancy value
						occ_bb = 0
						while(occ):
							lowest = lsb(occ)
							index = math.trunc(math.log(lowest,2))
							occ_bb |= diag[index]
							occ ^= lowest
						#determine lower diagonal blocker
						left_block_index = 0
						for left in range(sq_index-1,0,-1):
							if (diag[left] & occ_bb) != 0:
								left_block_index = left
								break
						#determine upper diagonal blocker
						right_block_index = len(diag)-1
						for right in range(sq_index+1,len(diag)):
							if (diag[right] & occ_bb) != 0:
								right_block_index = right
								break
						#calculate possible moves
						bb_attacks = 0
						for i in range(left_block_index, sq_index):
							bb_attacks |= diag[i]
						for i in range(sq_index+1, right_block_index+1):
							bb_attacks |= diag[i]
						#add to hash table
						diag_attacks[key][sq][occ_bb] = bb_attacks			
					sq_index += 1
		return diag_attacks
		
		
class Move:
	def __init__(self, dest_sq, source_sq, promotedto = 0):
		#can this data be compacted into a single integer?
		self._dest_sq = dest_sq
		self._source_sq = source_sq
		self._promotedto = promotedto
		return
		
	def __repr__(self):
		out = algebraic(self.getsourcesq()) + str('->') + algebraic(self.getdestsq()) 
		if self._promotedto != 0:
			out += str(' promo:' ) + str(self.getpromotedto())
		return out
		
	#to allow the possibility of changing storage structure of move data
	def getsourcesq(self):
		return self._source_sq
		
	def getdestsq(self):
		return self._dest_sq
		
	def getpromotedto(self):
		return self._promotedto
		
	def setpromotedto(self, promotion):
		self._promotedto = promotion
		return
		
class MoveGenerator:
	def __init__(self,transtable,preprocmoves):
		#preprocessed moves
		self._preprocmoves = deepcopy(preprocmoves)
		#useful map for generating moves along diagonals for sliding pieces
		self._mapsqtodiag = getmapsqtodiag()
		return
	
	def update_position(self, pos):
		self._position = deepcopy(pos)
		return
		
	def getpseudolegalmoves(self, tomove):
		#generate pseudo legal moves
		moves = []
		moves.extend(self.knightmoves(tomove))
		moves.extend(self.pawnmoves(tomove))
		moves.extend(self.kingmoves(tomove))
		moves.extend(self.rookmoves(tomove))
		moves.extend(self.bishopmoves(tomove))
		moves.extend(self.queenmoves(tomove))
		return moves
		
	def getbestmovefromlist(self, tomove, moves):
		#evaluate best possible move from given list of moves
		evals = []
		nomoves = len(moves)
		for index in range(0,nomoves):
			#create copy of position
			tmp_position = deepcopy(self._position)
			#update position with move
			tmp_position.update(moves[index])
			#evaluate new position
			evals.append((index,tmp_position.evaluate()))
		#find maximum evaluation for white and minimum evaluation for black
		orderedmoves = sorted(evals, key = itemgetter(1),reverse = True)
		bestmove = moves[orderedmoves[0][0]]
		if tomove == BLACK:
			bestmove = moves[orderedmoves[nomoves-1][0]]
		return bestmove
		
	def getmove(self, tomove):
		#get pseudo legal moves
		moves = self.getpseudolegalmoves(tomove)
		#find best move
		move = self.getbestmovefromlist(tomove, moves)
		#check that we are not leaving king in check
		return move
		
	def knightmoves(self,tomove):
		piece_type = 'N'
		pieces = 'w_pieces'
		if tomove == BLACK:
			piece_type = 'n'
			pieces = 'b_pieces'
		knights = deepcopy(self._position.piece_bb[piece_type])
		movelist = []
		while (knights):
			#find the knight's position
			source_sq = lsb(knights)
			#clear source square
			knights ^= source_sq
			#find available moves
			targets = self._preprocmoves.knight[source_sq] & ~self._position.piece_bb[pieces]
			while (targets):
				dest_sq = lsb(targets)
				targets ^= dest_sq
				amove = Move(dest_sq,source_sq)
				movelist.append(amove)
		return movelist
		
	def kingmoves(self,tomove):
		piece_type = 'K'
		pieces = 'w_pieces'
		if tomove == BLACK:
			piece_type = 'k'
			pieces = 'b_pieces'
		king_sq = deepcopy(self._position.piece_bb[piece_type])
		movelist = []
		targets = self._preprocmoves.king[king_sq] & ~self._position.piece_bb[pieces]
		while (targets):
			dest_sq = lsb(targets)
			targets ^= dest_sq
			amove = Move(dest_sq,king_sq)
			movelist.append(amove)	
		return movelist
		
	def pawnmoves(self,tomove):
		piece_type = 'P'
		pieces = 'w_pieces'
		other_pieces = 'b_pieces'
		if tomove == BLACK:
			piece_type = 'p'
			pieces = 'b_pieces'
			other_pieces = 'w_pieces'
		pawns = deepcopy(self._position.piece_bb[piece_type])
		movelist = []
		while (pawns):
			#find the pawn's position
			source_sq = lsb(pawns)
			#clear source square
			pawns ^= source_sq
			#find available non-capturing moves
			#pawn can't make any non-capturing move if a white or black piece is in its way
			moves_nocapture = 0
			if tomove == WHITE:
				moves_nocapture =  self._preprocmoves.whitepawn[source_sq] & ~self._position.piece_bb['all_pieces']
			else:
				moves_nocapture =  self._preprocmoves.blackpawn[source_sq] & ~self._position.piece_bb['all_pieces']
			while (moves_nocapture):
				dest_sq = lsb(moves_nocapture)
				moves_nocapture ^= dest_sq
				#need to check for case where pawn moves forward two squares but has a blocking piece in front
				if abs(RANK[dest_sq]-RANK[source_sq]) ==  2:
					#determine intervening square
					inter_sq = 0
					if tomove == WHITE:
						inter_sq = dest_sq >> 8
					else:
						inter_sq = dest_sq << 8
					if (inter_sq & self._position.piece_bb['all_pieces']):
						#not a valid move so skip to top of while loop
						continue
				amove = Move(dest_sq,source_sq)
				movelist.append(amove)
			#next check for capturing moves
			moves_capture = 0
			if tomove == WHITE:
				#diagonal left
				capture_sq = source_sq << 9
				#dont include bitshift which cause a wrap around to other side of board
				#also dont want to capture diagonally left when at a7
				if capture_sq <= a8 and abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					moves_capture = capture_sq & self._position.piece_bb[other_pieces]
				#diagonal right
				capture_sq = source_sq << 7
				if abs(FILE[capture_sq]-FILE[source_sq]) == 1:
					moves_capture |= capture_sq & self._position.piece_bb[other_pieces]	
			else:
				#diagonal right
				capture_sq = source_sq >> 9
				#dont include bitshift which cause a wrap around to other side of board
				#also dont want to capture diagonally right when at h7
				if capture_sq >= h1 and abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					moves_capture = capture_sq & self._position.piece_bb[other_pieces]
				#diagonal left
				capture_sq = source_sq >> 7
				if abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					moves_capture |= capture_sq & self._position.piece_bb[other_pieces]	
			while (moves_capture):
				dest_sq = lsb(moves_capture)
				moves_capture ^= dest_sq
				amove = Move(dest_sq,source_sq)
				movelist.append(amove)
		#check for promotion movesq
		knightpromo = []
		for amove in movelist:
			if RANK[amove.getdestsq()] == 8 and tomove == WHITE:
				amove.setpromotedto('Q')
				knightpromo.append(Move(amove.getdestsq(),amove.getsourcesq(),'N'))
			if RANK[amove.getdestsq()] == 1 and tomove == BLACK:
				amove.setpromotedto('q')
				knightpromo.append(Move(amove.getdestsq(),amove.getsourcesq(),'n'))
		movelist.extend(knightpromo)
		#finally check for en-passant moves. This is a pain as need move history!
		return movelist
		
	def rookmoves(self,tomove):
		piece_type = 'R'
		if tomove == BLACK:
			piece_type = 'r'
		rooks = deepcopy(self._position.piece_bb[piece_type])
		movelist = []
		while (rooks):
			#find the rooks' position
			source_sq = lsb(rooks)
			#clear source square
			rooks ^= source_sq
			movelist.extend(self.get_rank_attacks(source_sq,tomove))
			movelist.extend(self.get_file_attacks(source_sq,tomove))
		return movelist
		
	def bishopmoves(self,tomove):
		piece_type = 'B'
		if tomove == BLACK:
			piece_type = 'b'
		bishops = deepcopy(self._position.piece_bb[piece_type])
		movelist = []
		while (bishops):
			#find the bishop positions
			source_sq = lsb(bishops)
			#clear source square
			bishops ^= source_sq
			movelist.extend(self.get_diag_attacks(source_sq,tomove))
		return movelist
		
	def queenmoves(self,tomove):
		piece_type = 'Q'
		if tomove == BLACK:
			piece_type = 'q'
		queen_sq = deepcopy(self._position.piece_bb[piece_type])
		movelist = []
		#check that there is a queen
		if queen_sq != 0:
			movelist.extend(self.get_diag_attacks(queen_sq,tomove))
			movelist.extend(self.get_file_attacks(queen_sq,tomove))
			movelist.extend(self.get_rank_attacks(queen_sq,tomove))
		return movelist
		
	def get_rank_attacks(self,source_sq,tomove):
		movelist = []
		pieces = 'w_pieces'
		if tomove == BLACK:
			pieces = 'b_pieces'
		#find occupancy value for rank
		rank_occ = self._position.piece_bb['all_pieces'] & (255 << 8*(RANK[source_sq]-1))
		#find available moves along rank
		targets = self._preprocmoves.rankattacks[source_sq][rank_occ] & ~self._position.piece_bb[pieces]
		while (targets):
			dest_sq = lsb(targets)
			targets ^= dest_sq
			amove = Move(dest_sq,source_sq)
			movelist.append(amove)
		return movelist
			
	def get_file_attacks(self,source_sq,tomove):
		movelist = []
		pieces = 'w_pieces'
		if tomove == BLACK:
			pieces = 'b_pieces'
		#find occupancy value for file
		file_occ = self._position.piece_bb['all_pieces'] & (mirror_rank1_to_hfile(255) << (8-FILE[source_sq]))
		#find available moves along file
		targets = self._preprocmoves.fileattacks[source_sq][file_occ] & ~self._position.piece_bb[pieces]
		while (targets):
			dest_sq = lsb(targets)
			targets ^= dest_sq
			amove = Move(dest_sq,source_sq)
			movelist.append(amove)
		return movelist
			
	def get_diag_attacks(self,source_sq,tomove):
		movelist = []
		pieces = 'w_pieces'
		if tomove == BLACK:
			pieces = 'b_pieces'
		#loop over both the north east and north west diagonal
		for key in ['NE','NW']:
			#find occupancy value for diagonal
			diag_occ = self._position.piece_bb['all_pieces'] & self._mapsqtodiag[key][source_sq]
			#find available moves along diagonal
			targets = self._preprocmoves.diagattacks[key][source_sq][diag_occ] & ~self._position.piece_bb[pieces]
			while (targets):
				dest_sq = lsb(targets)
				targets ^= dest_sq
				amove = Move(dest_sq,source_sq)
				movelist.append(amove)
		return movelist

#################################
#              Main             #
#################################

def main():
	#set-up
	tomove = WHITE
	board = Position(INIT_FEN)
	move_generator = MoveGenerator(0,PreProcessedMoves())
	move_generator.update_position(board)
	#generate moves
	nomoves = 20
	for i in range(1, nomoves+1):
		print 'Move: ' + str(i)
		if tomove == WHITE:
			print 'White to move' 
		else:
			print 'Black to move' 
		new_move = move_generator.getmove(tomove)
		print 'Move chosen: ' + str(new_move)
		board.update(new_move)
		move_generator.update_position(board)
		board.display()
		tomove ^= 1
	return


if __name__ == '__main__':
	#try:
		main()
	#except Exception as e:
		#print e







