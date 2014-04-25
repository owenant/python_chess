from copy import deepcopy
from operator import itemgetter
import random
import math
import logging

logging.basicConfig()
logger = logging.getLogger('')
logger.setLevel(logging.WARNING)

#next steps
#deal with king in check

#################################
#           Globals             #
#################################

#INIT_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR'
INIT_FEN = 'rnbqkbnr/pppppppP/8/8/8/8/PPPPPPP1/RNBQKBNR'
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
#        Useful functions       #
#################################

#long to bit string conversion
def bin(s):
	return str(s) if s <= 1 else bin(s >> 1) + str(s&1)

#for a given square convert long into algebraic notation
def algebraic(sq):
	fileset = 'abcdefgh'
	return fileset[FILE[sq]- 1] + str(RANK[sq])

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
		
#################################
#          Main Classes         #
#################################

class Position:
	def __init__(self,fen):
		#check format of fen code used to initialise the position
		Position.check_fen(fen)
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
		self.piece_bb['all_pieces'] = self.piece_bb['w_pieces'] | self.piece_bb['b_pieces']
		return
		
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
		print "\n"
		return
		
	#function to check formatting of fen code
	@staticmethod
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

#Generates and stores bitboards of squares attacked by each piece given an
#empty board
class PreProcessedAttacks:
	def __init__(self):
		#useful store of diagonals
		self.diagonals = {'NE': [[h1],[g1,h2],[f1,g2,h3],[e1,f2,g3,h4],[d1,e2,f3,g4,h5],[c1,d2,e3,f4,g5,h6],[b1,c2,d3,e4,f5,g6,h7],[a1,b2,c3,d4,e5,f6,g7,h8],[a2,b3,c4,d5,e6,f7,g8],[a3,b4,c5,d6,e7,f8],[a4,b5,c6,d7,e8],[a5,b6,c7,d8],[a6,b7,c8],[a7,b8],[a8]], 'NW': [[a1],[b1,a2],[c1,b2,a3],[d1,c2,b3,a4],[e1,d2,c3,b4,a5],[f1,e2,d3,c4,b5,a6],[g1,f2,e3,d4,c5,b6,a7],[h1,g2,f3,e4,d5,c6,b7,a8],[h2,g3,f4,e5,d6,c7,b8],[h3,g4,f5,e6,d7,c8],[h4,g5,f6,e7,d8],[h5,g6,f7,e8],[h6,g7,f8],[h7,g8],[h8]]}
		self.knight = PreProcessedAttacks.preproc_knightattacks()
		self.king = PreProcessedAttacks.preproc_kingattacks()
		self.whitepawn = PreProcessedAttacks.preproc_whitepawnattacks()
		self.blackpawn = PreProcessedAttacks.preproc_blackpawnattacks()
		self.rankattacks = PreProcessedAttacks.preproc_rankattacks()
		self.fileattacks = self.preproc_fileattacks()
		self.diagattacks = self.preproc_diagattacks()
		return
	
	@staticmethod
	def preproc_knightattacks():
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
		
	@staticmethod
	def preproc_kingattacks():
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
	
	@staticmethod
	def preproc_whitepawnattacks():
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
	
	@staticmethod
	def preproc_blackpawnattacks():
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
		
	@staticmethod
	def preproc_rankattacks():
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
			mirror_occ = PreProcessedAttacks.mirror_rank1_to_hfile(occupancy)
			for index in range(0,8):
				mirror_value = PreProcessedAttacks.mirror_rank1_to_hfile(self.rankattacks[first_rank[index]][occupancy])
				file_attacks[first_file[index]][mirror_occ] = mirror_value
				#copy accross to other files
				for file in range(2,9):
					file_attacks[first_file[index] << (file -1)][mirror_occ << (file - 1)] = mirror_value << (file - 1) 
		return file_attacks
	
	def preproc_diagattacks(self): 
		#first generate attacks along diagonals
		diag_attacks = {'NE':{},'NW':{}}
 		for sq in SQUARES:
				diag_attacks['NE'][sq] = {}
				diag_attacks['NW'][sq] = {}
		#loop over diagonals
		for key in ['NE','NW']:
			for diag in self.diagonals[key]:
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
		
	#mirror first rank of a bitboard onto the h-file. used to help generate file attacks from rank attacks
	@staticmethod
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
		
#generates bitboards of squares attacked by each piece when provided with a
#position object
class PseudoLegalAttackGenerator:
	def __init__(self, preprocattacks):
		#preprocessed moves
		self._preprocattacks = preprocattacks
		#generate a map from a square and a north-east or north-west direction key to a bitboard consisting of 1's along the chosen diagonal. Useful when generating diagonal moves for sliding pieces.
		diags_bb = {'NE': [], 'NW': []}
		for key in ['NE','NW']:
			for diag in self._preprocattacks.diagonals[key]:
				diag_bb = 0
				for sq in diag:
					diag_bb |= sq
				diags_bb[key].append(diag_bb)
		#map from square to diagonal bb
		self._mapsqtodiag = {'NE': {}, 'NW': {}}
		for key in ['NE','NW']:
			for index in range(0,len(self._preprocattacks.diagonals[key])):
				for sq in self._preprocattacks.diagonals[key][index]:
					self._mapsqtodiag[key][sq] = diags_bb[key][index]
		#attack maps
		self.attacks_to = {}
		self.attacks_from = {}
		return
		
	def knightattacks(self,pos):
		logger.info('PseudoLegalAttackGenerator::knightattacks - start')
		
		knights = deepcopy(pos.piece_bb['N'] |  pos.piece_bb['n'])
		while (knights):
			#find the knight's position
			source_sq = lsb(knights)
			#clear source square
			knights ^= source_sq
			#find available moves
			knightattacks = self._preprocattacks.knight[source_sq] 
			self.attacks_from[source_sq] |= knightattacks			
			while (knightattacks):
				dest_sq = lsb(knightattacks)
				knightattacks ^= dest_sq
				self.attacks_to[dest_sq] |= source_sq
				
		logger.info('PseudoLegalAttackGenerator::knightattacks - end')
		return 
		
	def kingattacks(self,pos): 
		logger.info('PseudoLegalAttackGenerator::kingattacks - start')
		
		kings = deepcopy(pos.piece_bb['K'] |  pos.piece_bb['k'])
		while (kings):
			#find the king's position
			source_sq = lsb(kings)
			#clear source square
			kings ^= source_sq
			#find available moves
			kingattacks = self._preprocattacks.king[source_sq] 
			self.attacks_from[source_sq] |= kingattacks			
			while (kingattacks):
				dest_sq = lsb(kingattacks)
				kingattacks ^= dest_sq
				self.attacks_to[dest_sq] |= source_sq
				
		logger.info('PseudoLegalAttackGenerator::kingattacks - end')
		
		return 
		
	def pawnattacks(self,pos):
		logger.info('PseudoLegalAttackGenerator::pawnattacks - start')
		
		pawns = deepcopy(pos.piece_bb['P'] | pos.piece_bb['p'])
		while (pawns):
			#find the pawn's position
			source_sq = lsb(pawns)
			#clear source square
			pawns ^= source_sq
			#determine pawn colour
			whitepawn = True 
			if (source_sq & pos.piece_bb['p']):
				whitepawn = False
			#find available non-capturing moves
			#pawn can't make any non-capturing move if a white or black piece is in its way
			attacks_nocapture = 0
			if whitepawn == True:
				attacks_nocapture =  self._preprocattacks.whitepawn[source_sq] & ~pos.piece_bb['all_pieces']
			else:
				attacks_nocapture =  self._preprocattacks.blackpawn[source_sq] & ~pos.piece_bb['all_pieces']
			pawnattacks = deepcopy(attacks_nocapture)
			#need to check for case where pawn moves forward two squares but has a blocking piece in front
			while (attacks_nocapture):
				dest_sq = lsb(attacks_nocapture)
				attacks_nocapture ^= dest_sq
				if abs(RANK[dest_sq]-RANK[source_sq]) ==  2:
					#determine intervening square
					inter_sq = 0
					if whitepawn == True:
						inter_sq = dest_sq >> 8
					else:
						inter_sq = dest_sq << 8
					if (inter_sq & pos.piece_bb['all_pieces']):
						#not a valid move
						pawnattacks ^= dest_sq
			#next check for capturing moves
			if whitepawn == True:
				#diagonal left
				capture_sq = source_sq << 9
				#dont include bitshift which cause a wrap around to other side of board
				#also dont want to capture diagonally left when at a7
				if capture_sq <= a8 and abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					pawnattacks |= capture_sq & pos.piece_bb['all_pieces']
				#diagonal right
				capture_sq = source_sq << 7
				if abs(FILE[capture_sq]-FILE[source_sq]) == 1:
					pawnattacks |= capture_sq & pos.piece_bb['all_pieces']	
			else:
				#diagonal right
				capture_sq = source_sq >> 9
				#dont include bitshift which cause a wrap around to other side of board
				#also dont want to capture diagonally right when at h7
				if capture_sq >= h1 and abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					pawnattacks |= capture_sq & pos.piece_bb['all_pieces']
				#diagonal left
				capture_sq = source_sq >> 7
				if abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					pawnattacks |= capture_sq & pos.piece_bb['all_pieces']	
			#finally check for en-passant moves. This is a pain as need move history!
			self.attacks_from[source_sq] |= pawnattacks
			while(pawnattacks):
				dest_sq = lsb(pawnattacks)
				pawnattacks ^= dest_sq
				self.attacks_to[dest_sq] |= source_sq
				
		logger.info('PseudoLegalAttackGenerator::pawnattacks - end')
		
		return 
		
	def rookattacks(self,pos):
		logger.info('PseudoLegalAttackGenerator::rookattacks - start')
		
		rooks = deepcopy(pos.piece_bb['R'] | pos.piece_bb['r'])
		while (rooks):
			#find the rooks' position
			source_sq = lsb(rooks)
			#clear source square
			rooks ^= source_sq
			rookattacks = self.get_rank_attacks(source_sq,pos)
			rookattacks |= self.get_file_attacks(source_sq,pos)
			self.attacks_from[source_sq] |= rookattacks
			while(rookattacks):
				dest_sq = lsb(rookattacks)
				rookattacks ^= dest_sq
				self.attacks_to[dest_sq] |= source_sq
		
		logger.info('PseudoLegalAttackGenerator::rookattacks - end')
		return 
		
	def bishopattacks(self,pos):
		logger.info('PseudoLegalAttackGenerator::bishopattacks - start')
		
		bishops = deepcopy(pos.piece_bb['B'] |pos.piece_bb['b'])
		while (bishops):
			#find the bishop positions
			source_sq = lsb(bishops)
			#clear source square
			bishops ^= source_sq
			bishopattacks = self.get_diag_attacks(source_sq,pos)
			self.attacks_from[source_sq] |= bishopattacks
			while(bishopattacks):
				dest_sq = lsb(bishopattacks)
				bishopattacks ^= dest_sq
				self.attacks_to[dest_sq] |= source_sq
				
		logger.info('PseudoLegalAttackGenerator::bishopattacks - end')
		return 
		
	def queenattacks(self,pos):
		logger.info('PseudoLegalAttackGenerator::queenattacks - start')
		
		queens = deepcopy(pos.piece_bb['Q'] | pos.piece_bb['q'])
		while(queens):
			#find the queen positions
			source_sq = lsb(queens)
			#clear source square
			queens ^= source_sq
			queenattacks = self.get_diag_attacks(source_sq,pos)
			queenattacks |= self.get_file_attacks(source_sq,pos)
			queenattacks |= self.get_rank_attacks(source_sq,pos)
			self.attacks_from[source_sq] |= queenattacks
			while(queenattacks):
				dest_sq = lsb(queenattacks)
				queenattacks ^= dest_sq
				self.attacks_to[dest_sq] |= source_sq
		
		logger.info('PseudoLegalAttackGenerator::queenattacks - end')
		return 
		
	def get_rank_attacks(self,source_sq,pos):
		#find occupancy value for rank
		rank_occ = pos.piece_bb['all_pieces'] & (255 << 8*(RANK[source_sq]-1))
		#find available moves along rank
		rankattacks = self._preprocattacks.rankattacks[source_sq][rank_occ] 
		return rankattacks
			
	def get_file_attacks(self,source_sq,pos):
		#find occupancy value for file
		file_occ = pos.piece_bb['all_pieces'] & (PreProcessedAttacks.mirror_rank1_to_hfile(255) << (8-FILE[source_sq]))
		#find available moves along file
		fileattacks = self._preprocattacks.fileattacks[source_sq][file_occ] 
		return fileattacks
			
	def get_diag_attacks(self,source_sq,pos):
		#loop over both the north east and north west diagonal
		diagonalattacks = 0
		for key in ['NE','NW']:
			#find occupancy value for diagonal
			diag_occ = pos.piece_bb['all_pieces'] & self._mapsqtodiag[key][source_sq]
			#find available moves along diagonal
			diagonalattacks |= self._preprocattacks.diagattacks[key][source_sq][diag_occ] 
		return diagonalattacks
		
	#generate attacks
	def generateattacks(self,pos):
		for sq in SQUARES:
			self.attacks_to[sq] = 0
			self.attacks_from[sq] = 0
		self.knightattacks(pos)
		self.pawnattacks(pos)
		self.kingattacks(pos)
		self.rookattacks(pos)
		self.bishopattacks(pos)
		self.queenattacks(pos)
		return
				
		
class Evaluation:
	def __init__(self):
		#parameters for position evaluatiom
		self.piecevalue = {'Q': 9, 'R': 5, 'B': 3, 'N': 3, 'P': 1}
		return
		
	#main position evaluation function
	def evaluate(self, pos):
		#calculate material imbalance
		eval = self.materialimbalance(pos)
		return eval
		
	def materialimbalance(self,pos):
		eval = 0
		for piece in 'PRNBQ':
			eval += self.piecevalue[piece]*(pos.piece_count[piece] - pos.piece_count[piece.lower()])
		return eval
		
		
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
	def __init__(self, pseudoattacks, evaluator):
		self._pseudoattacks = pseudoattacks
		self._evaluator = evaluator
		return
		
	def getmove(self, tomove, pos):
		#generate all possible attacks
		movelist = []
		pieces = 'w_pieces'
		if tomove == BLACK:
			pieces = 'b_pieces'
		self._pseudoattacks.generateattacks(pos)
		attacks_from = self._pseudoattacks.attacks_from
		for sq in SQUARES:
			if (sq & pos.piece_bb[pieces]):
				attacks = deepcopy(attacks_from[sq])
				while (attacks):
					dest_sq = lsb(attacks)
					attacks ^= dest_sq
					#check not attacking a piece of the same colour
					if not (dest_sq & pos.piece_bb[pieces]):
						amove = Move(dest_sq,sq)
						movelist.append(amove)
		#check for promotions 
		for amove in movelist:
			#check to see if we have a pawn move
			if tomove == WHITE:
				if(amove.getsourcesq() & pos.piece_bb['P']):
					if RANK[amove.getdestsq()] == 8:
						amove.setpromotedto('Q')
						movelist.append(Move(amove.getdestsq(),amove.getsourcesq(),'N'))
			else:
				if(amove.getsourcesq() & pos.piece_bb['p']):
					if RANK[amove.getdestsq()] == 8:
						amove.setpromotedto('q')
						movelist.append(Move(amove.getdestsq(),amove.getsourcesq(),'n'))
		#find best move
		bestmove = self.getbestmovefromlist(tomove,movelist,pos)
		#check that we are not leaving king in check
		if self.check(bestmove,pos):
			print 'check: illegal move'
		return bestmove
		
	def check(self,move,pos):
		return False
	
	def getbestmovefromlist(self, tomove, moves, pos):
		#evaluate best possible move from given list of moves
		evals = []
		nomoves = len(moves)
		#evaluate current position
		currenteval = self._evaluator.evaluate(pos)
		for index in range(0,nomoves):
			#create copy of position
			tmp_position = deepcopy(pos)
			#update position with move
			tmp_position.update(moves[index])
			#evaluate new position
			evals.append((index,self._evaluator.evaluate(tmp_position)))
		#find maximum evaluation for white and minimum evaluation for black
		orderedmoves = sorted(evals, key = itemgetter(1),reverse = True)
		bestmove = moves[orderedmoves[0][0]]
		eval = orderedmoves[0][1]
		if tomove == BLACK:
			bestmove = moves[orderedmoves[nomoves-1][0]]
			eval = orderedmoves[nomoves-1][1]
		if eval == currenteval:
			bestmove = random.choice(moves)
		return bestmove
		

#################################
#              Main             #
#################################

def main():
	#set-up
	tomove = WHITE
	board = Position(INIT_FEN)
	pseudoattacks = PseudoLegalAttackGenerator(PreProcessedAttacks())
	evaluator = Evaluation()
	move_generator = MoveGenerator(pseudoattacks,evaluator)
	#generate moves
	nomoves = 1
	for i in range(1, nomoves+1):
		print 'Move: ' + str(i)
		if tomove == WHITE:
			print 'White to move' 
		else:
			print 'Black to move' 
		new_move = move_generator.getmove(tomove,board)
		print 'Move chosen: ' + str(new_move)
		board.update(new_move)
		board.display()
		print 'Evaluation: ' + str(evaluator.evaluate(board)) + '\n'
		tomove ^= 1
	return


if __name__ == '__main__':
	#try:
		main()
	#except Exception as e:
		#print e







