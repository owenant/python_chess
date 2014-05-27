from copy import deepcopy
from operator import itemgetter
import random
import math
import logging
import sys
import pdb

logging.basicConfig()
logger = logging.getLogger('')
logger.setLevel(logging.WARNING)

#next steps
#remove asymmetry wrt to pawns from attacks_from and attacks_to map, but check in getmove for diagonal capturing moves?

#################################
#           Globals             #
#################################

INIT_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR'
#INIT_FEN = '8/7k/8/4p2P/B7/P3K3/P7/8'
WHITE = 1
BLACK = 0
#define global variables that use square coordinates as names and contain the equivalent long. Also store in a list to iterate over, and also rank and file number associated with each square. Black's back rank is defined to be the 8th rank, and file a the first file
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
#define globals which store the diagonals 
DIAGONALS = {'NE': [[h1],[g1,h2],[f1,g2,h3],[e1,f2,g3,h4],[d1,e2,f3,g4,h5],[c1,d2,e3,f4,g5,h6],[b1,c2,d3,e4,f5,g6,h7],[a1,b2,c3,d4,e5,f6,g7,h8],[a2,b3,c4,d5,e6,f7,g8],[a3,b4,c5,d6,e7,f8],[a4,b5,c6,d7,e8],[a5,b6,c7,d8],[a6,b7,c8],[a7,b8],[a8]], 'NW': [[a1],[b1,a2],[c1,b2,a3],[d1,c2,b3,a4],[e1,d2,c3,b4,a5],[f1,e2,d3,c4,b5,a6],[g1,f2,e3,d4,c5,b6,a7],[h1,g2,f3,e4,d5,c6,b7,a8],[h2,g3,f4,e5,d6,c7,b8],[h3,g4,f5,e6,d7,c8],[h4,g5,f6,e7,d8],[h5,g6,f7,e8],[h6,g7,f8],[h7,g8],[h8]]}


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
	
#From a square and a north-east or north-west direction key generate a bitboard consisting of 1's along the chosen diagonal.
#@memoise
def sq_to_diagonal_bb(direction,source_sq):
	diag_bb = 0
	for diag in DIAGONALS[direction]:
		if source_sq in diag:
			for sq in diag:
				diag_bb |= sq
			return diag_bb
		
#################################
#          Main Classes         #
#################################

class Position:
	def __init__(self,fen):
		logger.info('Position::__init__ - start')
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
		
		logger.info('Position::__init__ - end')
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
					self.piece_count[piece] -= 1
					self.piece_count[promotedto]  += 1
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
		
	#function to return fen string for position
	def create_fen(self):
		board_array = [1 for x in range(0,64)]
		for piece in 'PRNBQKprnbqk':
			tmp_bb = deepcopy(self.piece_bb[piece])
			while(tmp_bb):
				sq = lsb(tmp_bb)
				tmp_bb ^= sq
				file = FILE[sq]
				rank = RANK[sq]
				#fen string starts with 8th rank, so need to reflect board 
				rank = 9 - rank
				board_array[(rank-1)*8 + (file - 1)] = piece
		count =  0
		for index in range(8,64,8):
			board_array.insert(index+count,'/')
			count += 1
		#reduce array by summing up 1's
		index = 1
		file = 1
		while(index < len(board_array)):
			if board_array[index] in range(1,8-file +  1): 
				if board_array[index - 1] in range(1,8):
					board_array[index - 1] = board_array[index] + board_array[index-1]
					board_array.pop(index)
				else:
					index += 1
			else:
				index += 1
			file = file % 8 
		#construct fen string from board_array
		fen_str = ''
		for index in range(0,len(board_array)):
			fen_str += str(board_array[index])
		return fen_str
	
#Generates and stores bitboards of squares attacked by each piece given an
#empty board
class PreProcessedAttacks:
	def __init__(self):
		#useful store of diagonals
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
			for diag in DIAGONALS[key]:
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
		#attack maps
		self._attacks_to = {}
		self._attacks_from = {}
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
			diag_occ = pos.piece_bb['all_pieces'] & sq_to_diagonal_bb(key,source_sq)
			#find available moves along diagonal
			diagonalattacks |= self._preprocattacks.diagattacks[key][source_sq][diag_occ] 
		return diagonalattacks
	
	#generate pawns moves that do not involve capturing another piece
	def get_pawn_noncapture_attacks(self,source_sq,pos):
		attacks_nocapture = 0
		if source_sq & (pos.piece_bb['P'] | pos.piece_bb['p']) != 0:
			whitepawn = True 
			if (source_sq & pos.piece_bb['p']):
				whitepawn = False
			#pawn can't make any non-capturing move if a white or black piece is in its way
			tmp_attacks_nocapture = 0
			if whitepawn == True:
				tmp_attacks_nocapture =  self._preprocattacks.whitepawn[source_sq] & ~pos.piece_bb['all_pieces']
			else:
				tmp_attacks_nocapture =  self._preprocattacks.blackpawn[source_sq] & ~pos.piece_bb['all_pieces']
			attacks_nocapture = deepcopy(tmp_attacks_nocapture)
			#need to check for case where pawn moves forward two squares but has a blocking piece in front
			while (tmp_attacks_nocapture):
				dest_sq = lsb(tmp_attacks_nocapture)
				tmp_attacks_nocapture ^= dest_sq
				if abs(RANK[dest_sq]-RANK[source_sq]) ==  2:
					#determine intervening square
					inter_sq = 0
					if whitepawn == True:
						inter_sq = dest_sq >> 8
					else:
						inter_sq = dest_sq << 8
					if (inter_sq & pos.piece_bb['all_pieces']):
						#not a valid move
						attacks_nocapture ^= dest_sq
		return attacks_nocapture
		
	#generate pawns moves that do involve capturing another piece
	def get_pawn_capture_attacks(self,source_sq,pos):
		attacks_capture = 0
		if source_sq & (pos.piece_bb['P'] | pos.piece_bb['p']) != 0:
			whitepawn = True 
			if (source_sq & pos.piece_bb['p']):
				whitepawn = False
			if whitepawn == True:
				#diagonal left
				capture_sq = source_sq << 9
				#dont include bitshift which cause a wrap around to other side of board
				#also dont want to capture diagonally left when at a7
				if capture_sq <= a8 and abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					attacks_capture |= capture_sq & pos.piece_bb['all_pieces']
				#diagonal right
				capture_sq = source_sq << 7
				if abs(FILE[capture_sq]-FILE[source_sq]) == 1:
					attacks_capture |= capture_sq & pos.piece_bb['all_pieces']	
			else:
				#diagonal right
				capture_sq = source_sq >> 9
				#dont include bitshift which cause a wrap around to other side of board
				#also dont want to capture diagonally right when at h7
				if capture_sq >= h1 and abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					attacks_capture |= capture_sq & pos.piece_bb['all_pieces']
				#diagonal left
				capture_sq = source_sq >> 7
				if abs(FILE[capture_sq]-FILE[source_sq]) ==  1:
					attacks_capture |= capture_sq & pos.piece_bb['all_pieces']	
		return attacks_capture
			
	#TODO:pawn en-passant attacks
	def get_pawn_enpassant_attacks(self,source_sq,pos):
		attacks_enpassant = 0
		return attacks_enpassant
		
	#generate all attacks
	#pawns are a little awkward. attacks_from contains all possible pawn moves
	#whereas attacks_to will only contain diagonal capturing moves. This must be kept in mind during move generation. The alternative is making pawns a special case which will increase the length of a lot of the move generation code and make the code more difficult to read.
	def get_attacks(self,pos):
		for sq in SQUARES:
			self._attacks_to[sq] = 0
			self._attacks_from[sq] = 0
		for piece in 'PRNBQK':
			piece_positions = deepcopy(pos.piece_bb[piece] | pos.piece_bb[piece.lower()])
			while(piece_positions):
				#find the piece squares
				source_sq = lsb(piece_positions)
				#clear source square
				piece_positions ^= source_sq
				attacks = self.get_attacks_from(source_sq,pos)
				self._attacks_from[source_sq] |= attacks
				while(attacks):
					dest_sq = lsb(attacks)
					attacks ^= dest_sq
					if (piece != 'P' or dest_sq & pos.piece_bb['all_pieces'] != 0):
						#for pawns attacks_to only contains capturing moves
						self._attacks_to[dest_sq] |= source_sq
		#to avoid just grabbing these attack maps without ensuring they apply to
		#the correct position, we keep them as 'private' member variables
		attacks = {'to': deepcopy(self._attacks_to), 'from':deepcopy(self._attacks_from)}
		return attacks
	
	#function to generate attacks from a given square
	def get_attacks_from(self,source_sq,pos):
		attacks = 0
		if source_sq & pos.piece_bb['all_pieces'] == 0:
			attacks = 0
		elif source_sq & (pos.piece_bb['Q'] | pos.piece_bb['q']) != 0:
			attacks = self.get_diag_attacks(source_sq,pos)
			attacks |= self.get_file_attacks(source_sq,pos)
			attacks |= self.get_rank_attacks(source_sq,pos)
		elif source_sq & (pos.piece_bb['B'] | pos.piece_bb['b']) != 0:
			attacks = self.get_diag_attacks(source_sq,pos)
		elif source_sq & (pos.piece_bb['R'] | pos.piece_bb['r']) != 0:
			attacks = self.get_file_attacks(source_sq,pos)
			attacks |= self.get_rank_attacks(source_sq,pos)
		elif source_sq & (pos.piece_bb['N'] | pos.piece_bb['n']) != 0:
			attacks = self._preprocattacks.knight[source_sq]
		elif source_sq & (pos.piece_bb['K'] | pos.piece_bb['k']) != 0:
			attacks = self._preprocattacks.king[source_sq] 
		elif source_sq & (pos.piece_bb['P'] | pos.piece_bb['p']) != 0:
			attacks = self.get_pawn_noncapture_attacks(source_sq,pos) | self.get_pawn_capture_attacks(source_sq,pos) | self.get_pawn_enpassant_attacks(source_sq,pos) 
		return attacks	
			
class Evaluation:
	def __init__(self):
		#parameters for position evaluation
		#piece values, taken from shatranj python chess engine
		self._piece_value_weight = 1
		self._piece_value= {'K': 40000, 'Q': 891, 'R': 561, 'B': 344, 'N': 322, 'P': 100}
		#piece position value, taken from shatranj python chess engine
		self._piece_position_weight = 1
		self._piece_square_value = {}
		self._piece_square_value['P'] = {}
		self._piece_square_value['p'] = {}
		self._piece_square_value['N'] = {}
		self._piece_square_value['n'] = {}
		self._piece_square_value['B'] = {}
		self._piece_square_value['b'] = {}
		self._piece_square_value['R'] = {}
		self._piece_square_value['r'] = {}
		self._piece_square_value['Q'] = {}
		self._piece_square_value['q'] = {}
		self._piece_square_value['K'] = {}
		self._piece_square_value['k'] = {}

		bp = [ 0, 0, 0, 0, 0, 0, 0, 0,
					2,  3,  4,  0,  0,  4,  3,  2, 
					4,  6, 12, 12, 12,  4,  6,  4,
					4,  7, 18, 25, 25, 16,  7,  4,
					6, 11, 18, 27, 27, 16, 11,  6,
					10, 15, 24, 32, 32, 24, 15, 10,
					10, 15, 24, 32, 32, 24, 15, 10,
					0,  0,  0,  0,  0,  0,  0,  0 ]

		wp = [ 0, 0,  0,  0,  0,  0,  0,  0,   
					10, 15, 24, 32, 32, 24, 15, 10,
					10, 15, 24, 32, 32, 24, 15, 10,
					6, 11, 18, 27, 27, 16, 11,  6,
					4,  7, 18, 25, 25, 16,  7,  4,
					4,  6, 12, 12, 12,  4,  6,  4,
					2,  3,  4,  0,  0,  4,  3,  2, 
					0,  0,  0,  0,  0,  0,  0,  0 ]

		bn = [-7, -3,  1,  3,  3,  1, -3, -7,
					2,  6, 14, 20, 20, 14,  6,  2,
					6, 14, 22, 26, 26, 22, 14,  6,
					8, 18, 26, 30, 30, 26, 18,  8,
					8, 18, 30, 32, 32, 30, 18,  8,
					6, 14, 28, 32, 32, 28, 14,  6,
					2,  6, 14, 20, 20, 14,  6,  2,
					-7, -3,  1,  3,  3,  1, -3, -7 ]

		wn = [-7, -3,  1,  3,  3,  1, -3, -7,
					2,  6, 14, 20, 20, 14,  6,  2,
					6, 14, 28, 32, 32, 28, 14,  6,
					8, 18, 30, 32, 32, 30, 18,  8,
					8, 18, 26, 30, 30, 26, 18,  8,
					6, 14, 22, 26, 26, 22, 14,  6,
					2,  6, 14, 20, 20, 14,  6,  2,
					-7, -3,  1,  3,  3,  1, -3, -7 ]

		bb = [ 16, 16, 16, 16, 16, 16, 16, 16,
					26, 29, 31, 31, 31, 31, 29, 26,
					26, 28, 32, 32, 32, 32, 28, 26,
					16, 26, 32, 32, 32, 32, 26, 16,
					16, 26, 32, 32, 32, 32, 26, 16,
					16, 28, 32, 32, 32, 32, 28, 16,
					16, 29, 31, 31, 31, 31, 29, 16,
					16, 16, 16, 16, 16, 16, 16, 16 ]

		wb = [ 16, 16, 16, 16, 16, 16, 16, 16,
					16, 29, 31, 31, 31, 31, 29, 16,
					16, 28, 32, 32, 32, 32, 28, 16,
					16, 26, 32, 32, 32, 32, 26, 16,
					16, 26, 32, 32, 32, 32, 26, 16,
					26, 28, 32, 32, 32, 32, 28, 26,
					26, 29, 31, 31, 31, 31, 29, 26,
					16, 16, 16, 16, 16, 16, 16, 16 ]

		br = [ 0,  0,  0,  3,  3,  0,  0,  0,
					-2,  0,  0,  0,  0,  0,  0, -2,
					-2,  0,  0,  0,  0,  0,  0, -2,
					-2,  0,  0,  0,  0,  0,  0, -2,
					-2,  0,  0,  0,  0,  0,  0, -2,
					-2,  0,  0,  0,  0,  0,  0, -2,
					10, 10, 10, 10, 10, 10, 10, 10,
					0,  0,  0,  0,  0,  0,  0,  0 ]

		wr = [ 0, 0,  0,  0,  0,  0,  0,  0,
					10, 10, 10, 10, 10, 10, 10, 10,
					-2, 0, 0, 0, 0, 0, 0, -2,
					-2, 0, 0, 0, 0, 0, 0, -2,
					-2, 0, 0, 0, 0, 0, 0, -2,
					-2, 0, 0, 0, 0, 0, 0, -2,
					-2, 0, 0, 0, 0, 0, 0, -2,
					0, 0, 0, 3, 3, 0, 0, 0 ]

		bq = [ -2, -2, -2, 0, 0, -2, -2, -2,
					0, 0, 1, 1, 1, 0, 0, 0,
					0, 1, 1, 1, 1, 0, 0, 0,
					0, 0, 0, 2, 2, 0, 0, 0,
					0, 0, 0, 2, 2, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0 ]

		wq = [ -2, -2, 0, 0, 0, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0,
					0, 0, 0, 2, 2, 0, 0, 0,
					0, 0, 0, 2, 2, 0, 0, 0,
 					0, 1, 1, 1, 1, 0, 0, 0,
 					0, 0, 1, 1, 1, 0, 0, 0,
 					-2, -2, -2, 0, 0, -2, -2, -2 ]

		bk = [ 3, 3, 8, -12,-8, -12,10, 5,
					-5, -5, -12,-12,-12,-12,-5, -5,
					-7, -15,-15,-15,-15,-15,-15,-7,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20 ]

		wk = [-20, -20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-7, -15,-15,-15,-15,-15,-15, -7,
					-5, -5,-12,-12,-12,-12, -5, -5,
					3, 3,  8,-12, -8,-12, 10,  5 ]
		
		for i in range(64):
			self._piece_square_value['P'][1L<<i] = wp[63-i]
			self._piece_square_value['p'][1L<<i] = bp[63-i]
			self._piece_square_value['N'][1L<<i] = wn[63-i]
			self._piece_square_value['n'][1L<<i] = bn[63-i]
			self._piece_square_value['B'][1L<<i] = wb[63-i]
			self._piece_square_value['b'][1L<<i] = bb[63-i]
			self._piece_square_value['R'][1L<<i] = wr[63-i]
			self._piece_square_value['r'][1L<<i] = br[63-i]
			self._piece_square_value['Q'][1L<<i] = wq[63-i]
			self._piece_square_value['q'][1L<<i] = bq[63-i]
			self._piece_square_value['K'][1L<<i] = wk[63-i]
			self._piece_square_value['k'][1L<<i] = bk[63-i]

		return
		
	#main position evaluation function
	def evaluate(self, pos):
		#calculate material imbalance
		eval = self._piece_value_weight * self.materialimbalance(pos)
		#piece position bonus
		eval += self._piece_position_weight * self.positionbonus(pos)
		return eval
		
	def materialimbalance(self,pos):
		eval = 0
		for piece in 'PRNBQK':
			eval += self._piece_value[piece]*(pos.piece_count[piece] - pos.piece_count[piece.lower()])
		return eval
		
	def positionbonus(self,pos):
		eval = 0
		multiplier = 1
		for piece in 'PpRrNnBbQqKk':
			tmp_pos = deepcopy(pos.piece_bb[piece])
			while(tmp_pos):
				sq = lsb(tmp_pos)
				tmp_pos ^= sq
				eval += multiplier * self._piece_square_value[piece][sq]
			multiplier *= -1
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
		#remember that attacks_from contains all possible pawn moves, whereas attacks_to only contains pawn capturing moves
		logger.info('MoveGenerator::getmove - start')
		
		movelist = []
		pieces = 'w_pieces'
		if tomove == BLACK:
			pieces = 'b_pieces'
		
		#generate all possible attacks
		attacks = self._pseudoattacks.get_attacks(pos)
		attacks_from = attacks['from']
		attacks_to = attacks['to']
		
		#check for check. use attacks_to here so that forward move by pawn cant put the king in check
		king_in_check = False
		if (attacks_to[pos.piece_bb['K']] & pos.piece_bb['b_pieces']) !=0 or (attacks_to[pos.piece_bb['k']] & pos.piece_bb['w_pieces']) !=0:
			king_in_check = True
			
		#generate possible moves
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
		knight_promotions = []
		for amove in movelist:
			#check to see if we have a pawn move
			if tomove == WHITE:
				if(amove.getsourcesq() & pos.piece_bb['P']):
					if RANK[amove.getdestsq()] == 8:
						amove.setpromotedto('Q')
						knight_promotions.append(Move(amove.getdestsq(),amove.getsourcesq(),'N'))
			else:
				if(amove.getsourcesq() & pos.piece_bb['p']):
					if RANK[amove.getdestsq()] == 1:
						amove.setpromotedto('q')
						knight_promotions.append(Move(amove.getdestsq(),amove.getsourcesq(),'n'))
		movelist.extend(knight_promotions)
		
		#determine evaluations of pseudo legal moves and arrange in order
		orderedmoves = self.get_ordered_evaluations(tomove,movelist,pos)
		print 'Ordered pseudo legal moves:' + str(orderedmoves)
		
		#evaluate current position
		currenteval = self._evaluator.evaluate(pos)
		
		#loop over ordered moves to determine best legal move. 
		best_legal_moves = []
		#get best evaluation based on pseudo legal moves
		best_eval = orderedmoves[0][1]
		for move_eval_pair in orderedmoves:
			move = move_eval_pair[0]
			eval = move_eval_pair[1]
			if ((tomove ==  WHITE and eval < best_eval) or (tomove == BLACK and eval > best_eval)) and len(best_legal_moves) > 0:
				#break out of loop if we have explored best moves and found one or more to be legal
				break
			if not self.pinned(tomove,move,pos,attacks_to,attacks_from):
				best_legal_moves.append(move_eval_pair)
		
		print 'Best legal moves:' + str(best_legal_moves)
		
		#check for stalemate and checkmate
		if len(best_legal_moves) == 0:
			if king_in_check == False:
				print 'Stalemate'
			else:
				print 'Checkmate'
			sys.exit()
		
		#choose a random move from best legal moves list
		tmp = random.choice(best_legal_moves)
		bestmove = tmp[0]
		bestmove_evaluation = tmp[1]
	
		#print result
		print 'Move chosen: ' + str(bestmove)
		print 'Evaluation: ' + str(bestmove_evaluation) + '\n'
		
		logger.info('MoveGenerator::getmove - end')
		return bestmove
		
	#check for pinned pieces 
	def pinned(self,tomove,move,pos,attacks_to,attacks_from):
		#check some simple conditions for it being a pinned piece, then if these
		#conditions are satisfied only then generate the piece moves that allow us to confirm the pin
		potential_pin = False
		king = 'k'
		sliding_pieces = 'BRQ'
		if tomove == WHITE:
			sliding_pieces = 'brq'
			king = 'K'
		#first we check if the piece is not the king as the king cannot be pinned
		if attacks_to[move.getsourcesq()] != 0 and (move.getsourcesq() & pos.piece_bb[king] == 0):
			#if piece is attacked it can only be pinned by a sliding piece		
			for attacking_piece in sliding_pieces:
				attacking_piece_pos = deepcopy(pos.piece_bb[attacking_piece])
				while(attacking_piece_pos):
					attacking_piece_sq = lsb(attacking_piece_pos)
					attacking_piece_pos ^= attacking_piece_sq
					if (attacks_from[attacking_piece_sq] & move.getsourcesq()) != 0:
						#piece can only be pinned if king, attacking piece and moving piece are aligned
						#check alignment along rank and file for queen and rook attacks
						if not attacking_piece in 'Bb':
							if (RANK[attacking_piece_sq] == RANK[move.getsourcesq()] == RANK[pos.piece_bb[king]]) or (FILE[attacking_piece_sq] == FILE[move.getsourcesq()] == FILE[pos.piece_bb[king]]):
								potential_pin = True
						#check alignment along diagonals for bishop and queen
						if not attacking_piece in 'Rr' and potential_pin == False:
							for key in ['NE','NW']:
								if (sq_to_diagonal_bb(key,move.getsourcesq()) == sq_to_diagonal_bb(key,attacking_piece_sq)) and (sq_to_diagonal_bb(key,attacking_piece_sq) == sq_to_diagonal_bb(key,pos.piece_bb[king])):
									potential_pin = True
						if potential_pin == True:
							#now update sliding piece moves once attacked piece has been moved, so that we can check for check
							tmp_position = deepcopy(pos)
							tmp_position.update(move)
							attacks = self._pseudoattacks.get_attacks_from(attacking_piece_sq,tmp_position)
							if attacks & pos.piece_bb[king] != 0:
								#exit function as soon as we discover a pin
								return True
		return False
	
	#returns moves and evaluations in order from best to worst
	def get_ordered_evaluations(self, tomove, movelist, pos):
		#evaluate best possible move from given list of moves
		evals = []
		#evaluate all given moves
		for move in movelist:
			#create copy of position
			tmp_position = deepcopy(pos)
			#update position with move
			tmp_position.update(move)
			#evaluate new position
			evals.append((move,self._evaluator.evaluate(tmp_position)))
		#order moves by evaluation
		orderedmoves = []
		if tomove == WHITE:
			orderedmoves = sorted(evals, key = itemgetter(1),reverse = True)
		else:
			orderedmoves = sorted(evals, key = itemgetter(1))
		return orderedmoves
		

#################################
#              Main             #
#################################

def main():
	#set-up
	tomove = WHITE
	#tomove = BLACK
	preprocessedattacks = PreProcessedAttacks()
	board = Position(INIT_FEN)
	pseudoattacks = PseudoLegalAttackGenerator(preprocessedattacks)
	evaluator = Evaluation()
	move_generator = MoveGenerator(pseudoattacks,evaluator)
	#generate moves
	nomoves = 20
	for i in range(1, nomoves+1):
		print 'Move: ' + str(i)
		if tomove == WHITE:
			print 'White to move' 
		else:
			print 'Black to move' 
		board.display()
		new_move = move_generator.getmove(tomove,board)
		board.update(new_move)
		print 'FEN: ' + str(board.create_fen())
		tomove ^= 1
	return


if __name__ == '__main__':
	#try:
		main()
	#except Exception as e:
		#print e







