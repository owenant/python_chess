from copy import deepcopy
from operator import itemgetter
import random
import math
import logging
import sys
import pdb
import time

#trick so that everything is printed in one go
sys.stdout = sys.stderr

logging.basicConfig()
logger = logging.getLogger('')
logger.setLevel(logging.WARNING)

#next steps
#king can stll move into check when capturing a piece

#################################
#           Globals             #
#################################

#player
WHITE = 1
BLACK = 0
#status and error flags
CHECKMATE = -3
STALEMATE = -2 
ILLEGAL_MOVE = -1
#define global variables that use algebraic notation to specify a square and contain the equivalent long. Also compute rank and file numbers associated with each square. Black's back rank is defined to be the 8th rank, and file a the first file.
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
#to deal with special case. can get rid of this when the king can no longer be taken
FILE[0] = RANK[0] = -1     
#define globals which store the diagonals 
DIAGONALS = {'NE': [[h1],[g1,h2],[f1,g2,h3],[e1,f2,g3,h4],[d1,e2,f3,g4,h5],[c1,d2,e3,f4,g5,h6],[b1,c2,d3,e4,f5,g6,h7],[a1,b2,c3,d4,e5,f6,g7,h8],[a2,b3,c4,d5,e6,f7,g8],[a3,b4,c5,d6,e7,f8],[a4,b5,c6,d7,e8],[a5,b6,c7,d8],[a6,b7,c8],[a7,b8],[a8]], 'NW': [[a1],[b1,a2],[c1,b2,a3],[d1,c2,b3,a4],[e1,d2,c3,b4,a5],[f1,e2,d3,c4,b5,a6],[g1,f2,e3,d4,c5,b6,a7],[h1,g2,f3,e4,d5,c6,b7,a8],[h2,g3,f4,e5,d6,c7,b8],[h3,g4,f5,e6,d7,c8],[h4,g5,f6,e7,d8],[h5,g6,f7,e8],[h6,g7,f8],[h7,g8],[h8]]}

#################################
#        Useful functions       #
#################################

def bin(s):
	"""Convert a long into a string of zeros and ones."""
	return str(s) if s <= 1 else bin(s >> 1) + str(s&1)

def algebraic(sq):
	"""For a given square convert associated long into algebraic notation."""
	fileset = 'abcdefgh'
	return fileset[FILE[sq]- 1] + str(RANK[sq])

def lsb(bb):
	"""Least signicant bit calculation for a long.
	
	This is useful in looping over occupied squares in a bitboard.
	"""
	return bb & -bb
	
def display_bb(bb):
		"""Provides text based visualisation of a bitboard.
		
		Only used when debugging code. """
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
	"""Encapsulates a board set-up.
	
	Represents state of chess board with bitboards for each piece type and colour. Also provides the functionality to update the position with a given move.
	"""
	def __init__(self, fen):
		"""Creates bitboards from a fen string."""
		logger.info('Position::__init__ - start')
		#check format of fen code used to initialise the position
		Position.check_fen(fen)
		#Dictionary to keep a count of the different type of pieces on the board. This to help speed up the evaluation function.
		self.piece_count = {k:0 for k in 'PRNBQKprnbqk'}
		#generate piece bitboards
		self.piece_bb = {k:0 for k in 'PRNBQKprnbqk'}
		ranks = fen.split("/")
		for k in 'PRNBQKprnbqk':
			index = 63
			for r in ranks:
				for sq in r:
					if (sq in '12345678'): 
						#we have a space move the index
						index -= int(sq)
					elif k == sq:
						#add piece at appropriate position in corresponding piece bitboard and increment count for this piece type.
						self.piece_bb[k] |= 1L << index
						self.piece_count[k] += 1
						index -= 1
					else:
						#a different type of piece
						index -= 1
		#generate bitboards for all white, all black pieces and all pieces. These are just useful conveniences.
		self.piece_bb['w_pieces'] = 0
		self.piece_bb['b_pieces'] = 0
		for k in 'PRNBQK':
			self.piece_bb['w_pieces'] |= self.piece_bb[k] 
		for k in 'prnbqk':
			self.piece_bb['b_pieces'] |= self.piece_bb[k] 
		self.piece_bb['all_pieces'] = self.piece_bb['w_pieces'] | self.piece_bb['b_pieces']
		#flags to track if castling move still possible i.e neither king or rooks have moved
		self.queen_side_castling = {'w_pieces': True, 'b_pieces': True}
		self.king_side_castling = {'w_pieces': True, 'b_pieces': True}
		
		logger.info('Position::__init__ - end')
		return
		
	def update(self, move):
		"""Update position with a given piece move."""
		source_sq = move.getsourcesq()
		dest_sq = move.getdestsq()
		promotedto = move.getpromotedto()
		#determine if this is a white or black move
		pieces = 'PRNBQK'
		other_pieces = 'prnbqk'
		piece_type = 'w_pieces'
		other_type = 'b_pieces'
		king = 'K'
		rook = 'R'
		tomove = WHITE
		#for castling
		king_side_king_destsq = {'w_pieces': g1, 'b_pieces': g8}
		queen_side_king_destsq  = {'w_pieces': c1, 'b_pieces': c8}
		king_side_rook_source_sq = {'w_pieces': h1, 'b_pieces': h8}
		king_side_rook_dest_sq = {'w_pieces': f1, 'b_pieces': f8}
		queen_side_rook_source_sq = {'w_pieces': a1, 'b_pieces': a8}
		queen_side_rook_dest_sq = {'w_pieces': d1, 'b_pieces': d8}
		king_start_sq = {'w_pieces': e1, 'b_pieces': e8}
		if (source_sq & self.piece_bb['b_pieces']):
			tomove = BLACK
			pieces = 'prnbqk'
			other_pieces = 'PRNBQK'
			piece_type = 'b_pieces'
			other_type = 'w_pieces'
			king = 'k'
			rook = 'r'
		#check to see if this is a castling move
		if self.king_side_castling[piece_type] == True and source_sq == king_start_sq[piece_type] and dest_sq == king_side_king_destsq[piece_type]:
			self.piece_bb[king] ^= king_start_sq[piece_type]
			self.piece_bb[king] ^= king_side_king_destsq[piece_type]
			self.piece_bb[rook] ^= king_side_rook_source_sq[piece_type]
			self.piece_bb[rook] ^= king_side_rook_dest_sq[piece_type]		
			self.king_side_castling[piece_type] = False
			self.queen_side_castling[piece_type] = False
		elif self.queen_side_castling[piece_type] == True and source_sq == king_start_sq[piece_type] and dest_sq == queen_side_king_destsq[piece_type]:
			self.piece_bb[king] ^= king_start_sq[piece_type]
			self.piece_bb[king] ^= queen_side_king_destsq[piece_type]
			self.piece_bb[rook] ^= queen_side_rook_source_sq[piece_type]
			self.piece_bb[rook] ^= queen_side_rook_dest_sq[piece_type]		
			self.king_side_castling[piece_type] = False
			self.queen_side_castling[piece_type] = False
		else:
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
			#check to see if this move prevents future castling
			if self.queen_side_castling[piece_type] == True or self.king_side_castling[piece_type] == True:
				#a king move will prevent both types of castling
				if source_sq & self.piece_bb[king]:
					self.king_side_castling[piece_type] = False
					self.queen_side_castling[piece_type] = False
			#check for rook move which prevents future king side castling
			if self.king_side_castling[piece_type] == True and source_sq == king_side_rook_source_sq[piece_type]:
				self.king_side_castling[piece_type] = False
			#and similarly for queen side castling
			if self.queen_side_castling[piece_type] == True and source_sq == queen_side_rook_source_sq[piece_type]:
				self.queen_side_castling[piece_type] = False
		#update general white and black piece bitboards
		self.piece_bb[piece_type] = 0
		for piece in pieces:
			self.piece_bb[piece_type] |= self.piece_bb[piece]
		#update all_pieces bitboard
		self.piece_bb['all_pieces'] = self.piece_bb['w_pieces'] | self.piece_bb['b_pieces']	
		return
		
	def display(self):
		"""Provides text based visualisation of board state."""
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
		
	@staticmethod
	def check_fen(fen):
		"""Check fen code has the correct format."""
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
		
	def create_fen(self):
		"""Create corresponding fen string from a given position."""
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
		fen_str = reduce(lambda x,y: str(x)+str(y), board_array)
		return fen_str
	
#Generates and stores bitboards of squares attacked by each piece given an
#empty board
class PreProcessedAttacks:
	"""Generates and stores bitboards of squares attacked by each piece.
	
	For kings, knights and pawns for each square and assuming an empty board, generate and store possible moves. For sliding pieces compute all possible moves along ranks, files and diagonals for all possible occupancy combinations. These pre-comouted bitboards help speed up move generation.
	""" 
	def __init__(self):
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
		"""Generates a bitboard per square indicating allowable knight moves."""
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
		"""Generates a bitboard per square indicating allowable king moves."""
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
		"""Generates a bitboard per square indicating allowable white pawn moves.
		
		Capturing and en-passant moves are determined in move generator.
		"""
		pawn = {}
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
		"""Generates a bitboard per square indicating allowable black pawn moves.
		
		Capturing and en-passant moves are determined in move generator.
		"""
		pawn = {}
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
		"""Generates a bitboard of possible moves along a rank by a sliding piece.
		
		This is done by square and by possible occupancy of squares along rank by other pieces.
		"""
		rank_attacks = {sq:{} for sq in SQUARES}
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
		"""Generates a bitboard of possible moves along a file by a sliding piece.
		
		This is done by square and by possible occupancy of squares along file by other pieces. This function assumes that moves along ranks have already been calculated and uses a reflection of these moves to compute moves along a file.
		"""
		file_attacks = {sq:{} for sq in SQUARES}
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
		"""Generates a bitboard of possible moves along a diagonal by a sliding piece.
		
		This is done by square and by possible occupancy of squares along diagonal  by other pieces.
		"""
		#first generate attacks along diagonals
		diag_attacks = {'NE':{sq:{} for sq in SQUARES},'NW':{sq:{} for sq in SQUARES}}
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
		
	@staticmethod
	def mirror_rank1_to_hfile(occupancy):
		"""Mirror first rank of a bitboard onto the h-file. 
		
		Used to help generate file attacks from rank attacks.
		"""
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
		

class PseudoLegalAttackGenerator:
	"""For a given position computes attacks from and attacks to a given square."""

	def __init__(self, preprocattacks):
		#preprocessed moves
		self._preprocattacks = preprocattacks
		#attack maps
		self._attacks_to = {sq:0 for sq in SQUARES}
		self._attacks_from = {sq:0 for sq in SQUARES}
		return
		
	def get_rank_attacks(self, source_sq, pos):
		"""For a given square and position compute possible attacks along a rank."""
		#find occupancy value for rank
		rank_occ = pos.piece_bb['all_pieces'] & (255 << 8*(RANK[source_sq]-1))
		#find available moves along rank
		rankattacks = self._preprocattacks.rankattacks[source_sq][rank_occ] 
		return rankattacks
			
	def get_file_attacks(self, source_sq, pos):
		"""For a given square and position compute possible attacks along a file."""
		#find occupancy value for file
		file_occ = pos.piece_bb['all_pieces'] & (PreProcessedAttacks.mirror_rank1_to_hfile(255) << (8-FILE[source_sq]))
		#find available moves along file
		fileattacks = self._preprocattacks.fileattacks[source_sq][file_occ] 
		return fileattacks
			
	def get_diag_attacks(self,source_sq,pos):
		"""For a given square and position compute possible attacks along a diagonal."""
		#loop over both the north east and north west diagonal
		diagonalattacks = 0
		for key in ['NE','NW']:
			#find occupancy value for diagonal
			diag_occ = pos.piece_bb['all_pieces'] & PseudoLegalAttackGenerator.sq_to_diagonal_bb(key,source_sq)
			#find available moves along diagonal
			diagonalattacks |= self._preprocattacks.diagattacks[key][source_sq][diag_occ] 
		return diagonalattacks
	
	def get_pawn_noncapture_attacks(self,source_sq,pos):
		"""Generate pawns moves that do not involve capturing another piece."""
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
		
	def get_pawn_capture_attacks(self,source_sq,pos):
		"""Generate pawns moves that involve capturing another piece."""
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
			
	def get_pawn_enpassant_attacks(self,source_sq,pos):
		"""TODO:pawn en-passant attacks."""
		attacks_enpassant = 0
		return attacks_enpassant
		
	def get_attacks(self,pos):
		"""Generate all attacks.
		
		Pawns are a little awkward. attacks_from contains all possible pawn moves
		whereas attacks_to will only contain diagonal capturing moves. This must be kept in mind during move generation. The alternative is making pawns a special case which will increase the length of a lot of the move generation code.
		"""
		self._attacks_to = {sq:0 for sq in SQUARES}
		self._attacks_from = {sq:0 for sq in SQUARES}
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
	
	def get_attacks_from(self,source_sq,pos):
		"""Generate attacks from a given square."""
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
		
	@staticmethod
	def sq_to_diagonal_bb(direction,source_sq):
		"""From a square and a north-east or north-west direction key generate a bitboard consisting of 1's along the chosen diagonal."""
		diag_bb = 0
		for diag in DIAGONALS[direction]:
			if source_sq in diag:
				for sq in diag:
					diag_bb |= sq
				return diag_bb
		
			
class Evaluation:
	"""Responsible for associating a numerical evaluation of a given position.
	
	Determines material imbalance and also gives weight to simple poistioning of pieces on board, e.g pawns attacking centre, rook on 7th file etc.
	"""
	def __init__(self):
		"""Contains parameters for position evaluation."""
		#piece values, taken from shatranj python chess engine
		self._piece_value_weight = 1
		#so that checkmate gives evaluation function an arbitrarily high score
		self._checkmate_value = 40000
		self._piece_value= {'Q': 891, 'R': 561, 'B': 344, 'N': 322, 'P': 100}
		#piece position value, taken from shatranj python chess engine
		self._piece_position_weight = 1
		self._piece_square_value = {piece:{} for piece in 'prnbqkPRNBQK'}

		p = [ 0, 0, 0, 0, 0, 0, 0, 0,
					2,  3,  4,  0,  0,  4,  3,  2, 
					4,  6, 12, 12, 12,  4,  6,  4,
					4,  7, 18, 25, 25, 16,  7,  4,
					6, 11, 18, 27, 27, 16, 11,  6,
					10, 15, 24, 32, 32, 24, 15, 10,
					10, 15, 24, 32, 32, 24, 15, 10,
					0,  0,  0,  0,  0,  0,  0,  0 ]

		P = [ 0, 0,  0,  0,  0,  0,  0,  0,   
					10, 15, 24, 32, 32, 24, 15, 10,
					10, 15, 24, 32, 32, 24, 15, 10,
					6, 11, 18, 27, 27, 16, 11,  6,
					4,  7, 18, 25, 25, 16,  7,  4,
					4,  6, 12, 12, 12,  4,  6,  4,
					2,  3,  4,  0,  0,  4,  3,  2, 
					0,  0,  0,  0,  0,  0,  0,  0 ]

		n = [-7, -3,  1,  3,  3,  1, -3, -7,
					2,  6, 14, 20, 20, 14,  6,  2,
					6, 14, 22, 26, 26, 22, 14,  6,
					8, 18, 26, 30, 30, 26, 18,  8,
					8, 18, 30, 32, 32, 30, 18,  8,
					6, 14, 28, 32, 32, 28, 14,  6,
					2,  6, 14, 20, 20, 14,  6,  2,
					-7, -3,  1,  3,  3,  1, -3, -7 ]

		N = [-7, -3,  1,  3,  3,  1, -3, -7,
					2,  6, 14, 20, 20, 14,  6,  2,
					6, 14, 28, 32, 32, 28, 14,  6,
					8, 18, 30, 32, 32, 30, 18,  8,
					8, 18, 26, 30, 30, 26, 18,  8,
					6, 14, 22, 26, 26, 22, 14,  6,
					2,  6, 14, 20, 20, 14,  6,  2,
					-7, -3,  1,  3,  3,  1, -3, -7 ]

		b = [ 16, 16, 16, 16, 16, 16, 16, 16,
					26, 29, 31, 31, 31, 31, 29, 26,
					26, 28, 32, 32, 32, 32, 28, 26,
					16, 26, 32, 32, 32, 32, 26, 16,
					16, 26, 32, 32, 32, 32, 26, 16,
					16, 28, 32, 32, 32, 32, 28, 16,
					16, 29, 31, 31, 31, 31, 29, 16,
					16, 16, 16, 16, 16, 16, 16, 16 ]

		B = [ 16, 16, 16, 16, 16, 16, 16, 16,
					16, 29, 31, 31, 31, 31, 29, 16,
					16, 28, 32, 32, 32, 32, 28, 16,
					16, 26, 32, 32, 32, 32, 26, 16,
					16, 26, 32, 32, 32, 32, 26, 16,
					26, 28, 32, 32, 32, 32, 28, 26,
					26, 29, 31, 31, 31, 31, 29, 26,
					16, 16, 16, 16, 16, 16, 16, 16 ]

		r = [ 0,  0,  0,  3,  3,  0,  0,  0,
					-2,  0,  0,  0,  0,  0,  0, -2,
					-2,  0,  0,  0,  0,  0,  0, -2,
					-2,  0,  0,  0,  0,  0,  0, -2,
					-2,  0,  0,  0,  0,  0,  0, -2,
					-2,  0,  0,  0,  0,  0,  0, -2,
					10, 10, 10, 10, 10, 10, 10, 10,
					0,  0,  0,  0,  0,  0,  0,  0 ]

		R = [ 0, 0,  0,  0,  0,  0,  0,  0,
					10, 10, 10, 10, 10, 10, 10, 10,
					-2, 0, 0, 0, 0, 0, 0, -2,
					-2, 0, 0, 0, 0, 0, 0, -2,
					-2, 0, 0, 0, 0, 0, 0, -2,
					-2, 0, 0, 0, 0, 0, 0, -2,
					-2, 0, 0, 0, 0, 0, 0, -2,
					0, 0, 0, 3, 3, 0, 0, 0 ]

		q = [ -2, -2, -2, 0, 0, -2, -2, -2,
					0, 0, 1, 1, 1, 0, 0, 0,
					0, 1, 1, 1, 1, 0, 0, 0,
					0, 0, 0, 2, 2, 0, 0, 0,
					0, 0, 0, 2, 2, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0 ]

		Q = [ -2, -2, 0, 0, 0, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0,
					-2, -2, 0, 0, 0, 0, 0, 0,
					0, 0, 0, 2, 2, 0, 0, 0,
					0, 0, 0, 2, 2, 0, 0, 0,
 					0, 1, 1, 1, 1, 0, 0, 0,
 					0, 0, 1, 1, 1, 0, 0, 0,
 					-2, -2, -2, 0, 0, -2, -2, -2 ]

		k = [ 3, 3, 8, -12,-8, -12,10, 5,
					-5, -5, -12,-12,-12,-12,-5, -5,
					-7, -15,-15,-15,-15,-15,-15,-7,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20 ]

		K = [-20, -20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-20,-20,-20,-20,-20,-20,-20,-20,
					-7, -15,-15,-15,-15,-15,-15, -7,
					-5, -5,-12,-12,-12,-12, -5, -5,
					3, 3,  8,-12, -8,-12, 10,  5 ]
		
		piece_dict = {'p':p, 'r': r, 'n':n, 'b':b, 'q':q, 'k':k, 'P':P, 'R': R, 'N':N, 'B':B, 'Q':Q, 'K':K}
		self._piece_square_value = {piece:{1L<<i: piece_dict[piece][63-i] for i in range(64)} for piece in 'prnbqkPRNBQK'}
		return
		
	def evaluate(self, tomove, pos):
		"""Returns evaluation of passed position."""
		eval = 0
		#calculate material imbalance
		eval = self._piece_value_weight * self.materialimbalance(pos)
		#piece position bonus
		eval += self._piece_position_weight * self.positionbonus(pos)
		return eval
		
	def materialimbalance(self,pos):
		"""Calculates contribution to evaluation function coming from captured pieces."""
		eval = 0
		for piece in 'PRNBQ':
			eval += self._piece_value[piece]*(pos.piece_count[piece] - pos.piece_count[piece.lower()])
		return eval
		
	def positionbonus(self,pos):
		"""Calculates contribution to evaluation function coming from position of pieces on board (irrespective of position of other pieces)."""
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
		
	def get_checkmate_value(self, tomove):
		"""Return checkmate value"""
		value = deepcopy(self._checkmate_value)
		if tomove == WHITE:
			#white is checkmated and loses so need to take negative of checkmate value
			value *= -1.0 
		return value
		
		
class Move:
	"""Encapsulates a move.
	
	Contains integers for source and destination squares and a string to label a promotion.
	"""
	def __init__(self, dest_sq, source_sq, promotedto = 0):
		#can this data be compacted into a single integer?
		self._dest_sq = dest_sq
		self._source_sq = source_sq
		self._promotedto = promotedto
		return
		
	def __repr__(self):
		"""Ensures printing a move provides destination and source square in algebraic notation."""
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
	"""Responsible for taking generated pseudo-legal moves and determining best legal move.
	
	Takes generated attacks_to and attacks_from maps and converts them into legal move objects. Uses an alpha-beta search algorithim to determine best move."""
	def __init__(self, pseudoattacks, evaluator, treedepth):
		self._pseudoattacks = pseudoattacks
		self._evaluator = evaluator
		self._treedepth = treedepth
		
		#arbitrarly large number for search routine
		self._maxscore = 100000
		#keeps track of number of final leaf nodes searched in search algorithm. Used to help assess improvements to move ordering and search algorithm.
		self._nodes_searched = 0	
		return
		
	def getmove(self, tomove, pos):
		"""Call search function and generate a move."""
		self._nodes_searched = 0
		
		bestmove, alphabeta_score = self.alphabeta(tomove, pos, 0, self._treedepth, -self._maxscore, self._maxscore, self._maxscore)
	
		print 'Move chosen: ' + str(bestmove)
		print 'AlphaBeta score: ' + str(alphabeta_score)
		print 'No of nodes searched: ' + str(self._nodes_searched)
		
		status = 0
		if bestmove == 0 and alphabeta_score == self._evaluator.get_checkmate_value(tomove):
			status = CHECKMATE
		
		return bestmove, status
		
	def alphabeta(self, tomove, node_pos, depth, treedepth, alpha, beta, maxscore):
		"""Perform alpha-beta tree search recursively."""
		#generate node moves
		ordered_moves, status = self.tree_nodes(tomove, node_pos)	
		#stop search if checkmate found
		if (status == CHECKMATE):
			bestmove = 0
			alphabeta_result = self._evaluator.get_checkmate_value(tomove)
		else:
			if depth == treedepth:
				bestmove = ordered_moves[0][0]
				alphabeta_result = ordered_moves[0][1]
				self._nodes_searched += 1
			else:
				#we need the best alpha beta score for this node
				bestmove = ordered_moves[0][0]
				alphabeta_result = -1.0 * maxscore
				next_to_move = BLACK
				if tomove == BLACK:
					next_to_move = WHITE
					alphabeta_result *= -1
				for move_eval_pair in ordered_moves:
					move = move_eval_pair[0]
					if (tomove == WHITE and alphabeta_result < beta) or (tomove == BLACK and alphabeta_result > alpha):
						#take a copy of node position and call minimax again
						nextpos = deepcopy(node_pos)
						nextpos.update(move)
						amove,result = self.alphabeta(next_to_move, nextpos, depth+1, treedepth, alpha, beta, maxscore)
						if (tomove ==  WHITE and (result > alphabeta_result)):
							alphabeta_result = result
							bestmove = move
							alpha = max(alphabeta_result, alpha)
						elif (tomove == BLACK and (result < alphabeta_result)):
							alphabeta_result = result
							bestmove = move
							beta = min(alphabeta_result, beta)
					else:
						break
		return bestmove,alphabeta_result
		
	def tree_nodes(self, tomove, pos):
		"""Calculate possible legal moves for a given position."""
		#remember that attacks_from contains all possible pawn moves, whereas attacks_to only contains pawn capturing moves
		logger.info('MoveGenerator::tree_nodes - start')
		
		#generate all possible attacks
		attacks = self._pseudoattacks.get_attacks(pos)
		attacks_from = attacks['from']
		attacks_to = attacks['to']
		
		other_pieces = 'b_pieces'
		king = 'K'
		if tomove == BLACK:
			other_pieces = 'w_pieces'
			king = 'k'
		
		#see if king is in check
		king_in_check = False
		king_sq = lsb(pos.piece_bb[king])
		attacks_to[king_sq] 
		pos.piece_bb[other_pieces]
		if (attacks_to[king_sq] & pos.piece_bb[other_pieces]):
			king_in_check = True
		
		legal_moves = []
		status = 0
		#if king is in check use specific check evasion routine
		if king_in_check == True:
			legal_moves, status = self.generate_check_evasions(tomove,pos,attacks_to,attacks_from)
		else:
			#generate all possible legal moves 
			legal_moves, status  = self.generate_all_legal_moves(tomove,pos,attacks_to,attacks_from)
		
		#evaluate and order moves 
		ordered_moves = []
		for move in legal_moves:
			#create copy of position
			tmp_position = deepcopy(pos)
			#update position with move
			tmp_position.update(move)
			#evaluate new position
			ordered_moves.append((move,self._evaluator.evaluate(tomove, tmp_position)))
		#order moves
		reverse_flag = True
		if tomove == BLACK:
			reverse_flag = False
		ordered_moves = sorted(ordered_moves, key = itemgetter(1), reverse = reverse_flag)
		
		logger.info('MoveGenerator::tree_nodes - end')
		#return moves and evaluations separately
		return ordered_moves, status
		
	def generate_check_evasions(self,tomove,pos,attacks_to,attacks_from):
		"""Specific move generation for when king is in check."""
		#setup variables
		movelist = []
		checkmate_flag = False
		pieces = 'w_pieces'
		other_pieces = 'b_pieces'
		other_pawn = 'p'
		other_knight = 'n'
		other_sliding_pieces = 'qrb'
		king = 'K'
		if tomove == BLACK:
			pieces = 'b_pieces'
			other_pieces = 'w_pieces'
			other_pawn = 'P'
			other_knight = 'N'
			other_sliding_pieces = 'QRB'
			king = 'k'
			
		#determine number of pieces which are attacking the king
		king_sq = pos.piece_bb[king]
		attacks = deepcopy(attacks_to[king_sq] & pos.piece_bb[other_pieces])
		no_attacking_pieces = 0
		while (attacks):
			sq = lsb(attacks)
			attacks ^= sq
			no_attacking_pieces += 1
		
		#first generate moves that simply move king out of the way. These are the only check evasion moves that are possible in the case when more than one piece is attacking the king
		attacks = deepcopy(attacks_from[king_sq])
		while(attacks):
			dest_sq = lsb(attacks)
			attacks ^= dest_sq
			#check not attacking a piece of the same colour
			if not (dest_sq & pos.piece_bb[pieces]):
				#check move does not put king back in check
				move = Move(dest_sq,king_sq)
				if not self.king_move_into_check(tomove,move,pos,attacks_to,attacks_from):
					movelist.append(move)
		
		blocking_sqs = []			
		if no_attacking_pieces == 1:
			#if only one piece is attacking the king then it may be possible to capture the attacking piece
			attk_piece_sq = attacks_to[king_sq] & pos.piece_bb[other_pieces]
			attacks_to_threat = deepcopy(attacks_to[attk_piece_sq] & pos.piece_bb[pieces])
			while(attacks_to_threat):
				source_sq = lsb(attacks_to_threat)
				attacks_to_threat ^= source_sq
				movelist.append(Move(attk_piece_sq,source_sq))	
			#if attack is not by a pawn or knight might be possible to block it
			if not ((attacks_to[king_sq] & pos.piece_bb[other_pawn]) | (attacks_to[king_sq] & pos.piece_bb[other_knight])):
				#need to find if there any squares attacked by moving side that are along the diagonal, file or rank that attacks the king
				for attacking_piece in other_sliding_pieces:
					slide_sourcesq = attacks_to[king_sq] & pos.piece_bb[attacking_piece]
					if slide_sourcesq != 0:
						#is attack along a file?
						if attacking_piece in 'QqRr':
							if FILE[slide_sourcesq] == FILE[king_sq]:
								block_sq = min(slide_sourcesq,king_sq)
								while (block_sq < max(slide_sourcesq,king_sq) >> 8):			
									block_sq = block_sq << 8		
									blocking_sqs.append(block_sq)			
						#is attack along a rank?			
						if attacking_piece in 'QqRr':
							if RANK[slide_sourcesq] == RANK[king_sq]:
								block_sq = min(slide_sourcesq,king_sq)
								while (block_sq < max(slide_sourcesq,king_sq) >> 1):			
									block_sq = block_sq << 1
									blocking_sqs.append(block_sq)		
						#is attack along a diagonal?
						if attacking_piece in 'QqBb':
							if MoveGenerator.same_diag(king_sq,slide_sourcesq):
								#ne or nw diagonal?
								offset1 = FILE[king_sq] + 8*(RANK[king_sq]-1) 
								offset2 = FILE[slide_sourcesq] + 8*(RANK[slide_sourcesq]-1) 
								if (offset1 - offset2) % 9 == 0:
									mod_factor = 7
								else:
									mod_factor = 9
								block_sq = min(slide_sourcesq,king_sq)
								while (block_sq < max(slide_sourcesq,king_sq) >> mod_factor):	
									block_sq = block_sq << mod_factor
									blocking_sqs.append(block_sq)		
			#generate blocking moves now we know what squares can be used to block the check					
			for block_destsq in blocking_sqs:
				blocking_piece_sqs = attacks_to[block_destsq] & pos.piece_bb[pieces]
				while(blocking_piece_sqs):
					sq = lsb(blocking_piece_sqs)
					blocking_piece_sqs ^= sq
					if sq & pos.piece_bb[king] == 0:
						movelist.append(Move(block_destsq,sq))	
				
		#is it checkmate?
		status = 0
		if len(movelist) == 0:
			status = CHECKMATE
		
		return movelist, status
		
	def generate_all_legal_moves(self,tomove,pos,attacks_to,attacks_from):
		"""Generate all possible legal moves, guven that king is not in check."""
		
		pieces = 'w_pieces'
		other_pieces = 'b_pieces'
		king = 'K'
		other_king = 'k'
		if tomove == BLACK:
			pieces = 'b_pieces'
			other_pieces = 'w_pieces'
			king = 'k'
			other_king = 'K'
		
		movelist = []
		knight_promotions = []
		piece_sqs = deepcopy(pos.piece_bb[pieces])
		while(piece_sqs):
			sq = lsb(piece_sqs)
			piece_sqs ^= sq
			attacks = deepcopy(attacks_from[sq])
			while (attacks):
				dest_sq = lsb(attacks)
				attacks ^= dest_sq
				#check not attacking a piece of the same colour
				if not (dest_sq & pos.piece_bb[pieces]):
					amove = Move(dest_sq,sq)
					#check for promotion 
					if (MoveGenerator.pawn_promotion_check(tomove, pos, amove)):
						if tomove == WHITE:
							amove.setpromotedto('Q')
							knight_promotions.append(Move(dest_sq,sq,'N'))
						else:
							amove.setpromotedto('q')
							knight_promotions.append(Move(dest_sq,sq,'n'))
					movelist.append(amove)
		movelist.extend(knight_promotions)		
		
		#remove illegal moves. Slow way of doing things, first generating all moves and then removing all illegal moves. Performance is more critically dependent on search algorithm though?
		legal_moves = []
		for amove in movelist:
			#exclude moves from pinned pieces
			if self.pinned(tomove,amove,pos,attacks_to,attacks_from):
				continue 
			#exclude king moves that put king in check
			if amove.getsourcesq() & pos.piece_bb[king]:
				if attacks_to[amove.getdestsq()] & pos.piece_bb[other_pieces]:
					#note that in this case the king is not in check so we dont need to worry about updating sliding piece attacks
					continue
			#exclude moves that capture the king
			if amove.getdestsq() & pos.piece_bb[other_king]:
					continue
			legal_moves.append(amove)
		
		#castling
		if pos.queen_side_castling[pieces] == True or pos.king_side_castling[pieces] == True:
			castling_moves = self.generate_castling_moves(tomove,pos,attacks_to,attacks_from)
			legal_moves.extend(castling_moves)
		
		#is it stalemate?
		status = 0
		if len(movelist) == 0:
			status = STALEMATE
			
		return legal_moves, status
		
	def generate_castling_moves(self,tomove,pos,attacks_to,attacks_from):
		"""If conditions are met, generate castling move."""
		castling_moves = []
		pieces = 'w_pieces'
		other_pieces = 'b_pieces'
		king = 'K'
		other_king = 'k'
		queen_side_sqs = [e1,d1,c1,b1]
		king_side_sqs = [e1,f1,g1]
		if tomove == BLACK:
			pieces = 'b_pieces'
			other_pieces = 'w_pieces'
			king = 'k'
			other_king = 'K'
			queen_side_sqs = [e8,d8,c8,b8]
			king_side_sqs = [e8,f8,g8]
			
		#deal with king side castling first
		if pos.king_side_castling[pieces] == True:
			#check king does not move through or into check, also make sure king is not in check
			attacks_to_castling_sqs = 0
			for sq in king_side_sqs:
				attacks_to_castling_sqs |= attacks_to[sq]
			if not attacks_to_castling_sqs & pos.piece_bb[other_pieces]:
				#check no other pieces in the way
				if not (pos.piece_bb['all_pieces'] & king_side_sqs[2] | pos.piece_bb['all_pieces'] & king_side_sqs[1]):
					#clear to castle
					castling_moves.append(Move(king_side_sqs[2],king_side_sqs[0]))
		#next queen side castling
		if pos.queen_side_castling[pieces] == True:
			attacks_to_castling_sqs = 0
			for sq in queen_side_sqs:
				attacks_to_castling_sqs |= attacks_to[sq]
			if not attacks_to_castling_sqs & pos.piece_bb[other_pieces]:
				#check no other pieces in the way
				if not (pos.piece_bb['all_pieces'] & queen_side_sqs[3] | pos.piece_bb['all_pieces'] & queen_side_sqs[2] | pos.piece_bb['all_pieces'] & queen_side_sqs[1]):
					#clear to castle
					castling_moves.append(Move(queen_side_sqs[2],queen_side_sqs[0]))
		return castling_moves
		
	def king_move_into_check(self,tomove,move,pos,attacks_to,attacks_from):
		"""Check that king does not move into check"""
		pieces = 'w_pieces'
		other_pieces = 'b_pieces'
		sliding_pieces = 'qrb'
		if tomove == BLACK:
			pieces = 'b_pieces'
			other_pieces = 'w_pieces'
			sliding_pieces = 'QRB'
		
		king_moved_into_check = False
		king_destsq = move.getdestsq()
		king_sourcesq = move.getsourcesq()
		#first use a simple check
		if attacks_to[king_destsq] & pos.piece_bb[other_pieces]:
			king_moved_into_check = True
		
		#but still need to be careful with sliding pieces so that king, which would have been a blocker when generating a sliding piece move can not just move one square away along direction of attack.
		if king_moved_into_check == False:
			attacks = deepcopy(attacks_to[king_sourcesq] & pos.piece_bb[other_pieces])
			for attacking_piece in sliding_pieces:
				slider_sqs = deepcopy(pos.piece_bb[attacking_piece])
				while(slider_sqs):
					attacking_piece_sq = lsb(slider_sqs)
					slider_sqs ^= attacking_piece_sq
					if (attacking_piece_sq & attacks):
						#check alignment along rank and file for queen and rook attacks
						if not attacking_piece in 'Bb':
							if (RANK[attacking_piece_sq] == RANK[king_destsq]) or (FILE[attacking_piece_sq] == FILE[king_destsq]):
								king_moved_into_check = True
						#check alignment along diagonals for bishop and queen
						if not attacking_piece in 'Rr' and king_moved_into_check == False:
							if MoveGenerator.same_diag(king_destsq,attacking_piece_sq):
								king_moved_into_check = True
		
		return king_moved_into_check
		
	def pinned(self,tomove,move,pos,attacks_to,attacks_from):
		"""Check to see if move is possible or if piece is pinned.
		
		First checks some simple conditions for piece being pinned. If these
		conditions are satisfied then generate the piece moves that allow us to confirm the pin."""
		potential_pin = False
		king = 'k'
		sliding_pieces = 'BRQ'
		pieces = 'w_pieces'
		if tomove == WHITE:
			sliding_pieces = 'brq'
			pieces = 'b_pieces'
			king = 'K'
		#first we check that moving piece is being attacked by a piece and that it is not the king
		if (attacks_to[move.getsourcesq()] & pos.piece_bb[pieces] != 0) and (move.getsourcesq() & pos.piece_bb[king] == 0):
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
								if MoveGenerator.same_diag(move.getsourcesq(),attacking_piece_sq) and MoveGenerator.same_diag(attacking_piece_sq,pos.piece_bb[king]):
									potential_pin = True
						if potential_pin == True:
							#now update sliding piece moves once attacked piece has been moved, so that we can check for check
							tmp_position = deepcopy(pos)
							tmp_position.update(move)
							attacks = self._pseudoattacks.get_attacks_from(attacking_piece_sq,tmp_position)
							#check that we have not captured pinning piece
							if (attacking_piece_sq & tmp_position.piece_bb[pieces]) != 0:
								#check that pinning piece now attacks the king
								if (attacks & tmp_position.piece_bb[king]) != 0:
									#exit function as soon as we discover a pin
									return True
		return False
	
	def get_user_move(self, tomove, pos, source_str, dest_str):
		"""Convert string destination and source squares into a move.
		
		Checks for legality and promotions."""
		#compute possible legal moves
		ordered_moves, status = self.tree_nodes(tomove, pos)
		
		exec('dest_sq ='+ str(dest_str))
		exec('source_sq ='+ str(source_str))
		move = Move(dest_sq, source_sq)
		if (MoveGenerator.pawn_promotion_check(tomove, pos, move)):
			#TODO: also allow for knight promotions
			if tomove == WHITE:
				move.setpromotedto('Q')
			else:
				move.setpromotedto('q')
		
		#check for checkmate and move legality
		if status == CHECKMATE:
			move = 0
		else:
			status = ILLEGAL_MOVE
			for move_eval_pair in ordered_moves:
				amove = move_eval_pair[0]
				if move.getdestsq() == amove.getdestsq() and move.getsourcesq() == amove.getsourcesq():
					status = 0
					break
		
		return move, status
	
	@staticmethod
	def pawn_promotion_check(tomove, pos, move):
		"""Check if move can lead to a promotion."""
		promo = False
		dest_sq = move.getdestsq()
		source_sq = move.getsourcesq()
		if tomove == WHITE and RANK[dest_sq] == 8:
			if (source_sq & pos.piece_bb['P']) != 0:
				promo = True
		elif tomove == BLACK and RANK[dest_sq] == 1:
			if (source_sq & pos.piece_bb['p']) != 0:
				promo = True
		return promo
	
	@staticmethod			
	def same_diag(sq1,sq2):
		"""Return true if two squares belong to the same diagonal, otherwise return false."""
		offset1 = FILE[sq1] + 8*(RANK[sq1]-1) 
		offset2 = FILE[sq2] + 8*(RANK[sq2]-1) 
		if (offset1 - offset2) % 9 == 0 or (offset1 - offset2) % 7 == 0:
			return True
		return False

#################################
#              Main             #
#################################

def main():
	#set-up
	#initial_fen = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR'
	initial_fen = 'r2r3k/2p4p/p6B/2Pn1pR1/RP4p1/7P/1P3PP1/6K1'
	tomove = WHITE
	#tomove = BLACK
	search_depth = 2
	human_player = True
	
	#initialise objects
	preprocessedattacks = PreProcessedAttacks()
	board = Position(initial_fen)
	pseudoattacks = PseudoLegalAttackGenerator(preprocessedattacks)
	evaluator = Evaluation()
	move_generator = MoveGenerator(pseudoattacks,evaluator,search_depth)

	#display starting board
	print 'Starting position:'
	board.display()
	
	#generate moves
	nomoves = 150
	for move_no in range(1, nomoves+1):
		print 'Move: ' + str(move_no)
		if tomove == WHITE:
			print 'White to move' 
		else:
			print 'Black to move' 
		status = ILLEGAL_MOVE
		if human_player == True and move_no % 2 == 1:
			while status == ILLEGAL_MOVE:
				source_sq = raw_input("Source square: ").strip()
				dest_sq = raw_input("Destination square: ").strip()
				new_move, status = move_generator.get_user_move(tomove,board,source_sq,dest_sq)
				if status == ILLEGAL_MOVE:
					print 'Illegal move.'
		else:
			start = time.time()
			new_move, status = move_generator.getmove(tomove,board)
			end = time.time()
			print 'Elapsed time for move generation: ' + str(round(end - start,2)) + str('s')
		if status == CHECKMATE:
			print 'Checkmate.'
			break
		elif status == STALEMATE:
			print 'Stalemate.'
			break
		else:
			board.update(new_move)
			board.display()
			print 'FEN: ' + str(board.create_fen()) + '\n'
			tomove ^= 1
	return


if __name__ == '__main__':
	#try:
		main()
	#except Exception as e:
		#print e







