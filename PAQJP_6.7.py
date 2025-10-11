import os
import sys
import math
import struct
import array
import random
import heapq
import binascii
import logging
import paq  # pip install paq
import hashlib
from datetime import datetime
from enum import Enum
from typing import List, Dict, Tuple, Optional
import qiskit  # For quantum-inspired circuit definition

# Configure Logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler()]
)

# Constants
PROGNAME = "PAQJP_6.7"
HUFFMAN_THRESHOLD = 1024
PI_DIGITS_FILE = "pi_digits.txt"
PRIMES = [p for p in range(2, 256) if all(p % d != 0 for d in range(2, int(p**0.5)+1))]
MEM = 1 << 15
MIN_BITS = 2

# Dictionary Files (Unused by transform_11 and transform_54)
DICTIONARY_FILES = [
    "words_enwik8.txt", "eng_news_2005_1M-sentences.txt", "eng_news_2005_1M-words.txt",
    "eng_news_2005_1M-sources.txt", "eng_news_2005_1M-co_n.txt",
    "eng_news_2005_1M-co_s.txt", "eng_news_2005_1M-inv_so.txt",
    "eng_news_2005_1M-meta.txt", "Dictionary.txt",
    "the-complete-reference-html-css-fifth-edition.txt", "francais.txt", "espanol.txt",
    "deutsch.txt", "ukenglish.txt", "vertebrate-palaeontology-dict.txt", "dictionary.2.bin",
    "dictionary.1.bin", "dictionary.3.bin", "dictionary.4.bin", "dictionary.6.bin",
    "dictionary.7.bin", "dictionary.8.bin", "dictionary.9.bin", "dictionary.11.bin",
    "dictionary.12.bin", "dictionary.13.bin", "dictionary.14.bin", "dictionary.15.bin",
    "dictionary.16.bin", "dictionary.19.bin", "dictionary.20.bin"
]

# DNA Encoding Table
DNA_ENCODING_TABLE = {
    'AAAA': 0b00000, 'AAAC': 0b00001, 'AAAG': 0b00010, 'AAAT': 0b00011,
    'AACC': 0b00100, 'AACG': 0b00101, 'AACT': 0b00110, 'AAGG': 0b00111,
    'AAGT': 0b01000, 'AATT': 0b01001, 'ACCC': 0b01010, 'ACCG': 0b01011,
    'ACCT': 0b01100, 'AGGG': 0b01101, 'AGGT': 0b01110, 'AGTT': 0b01111,
    'CCCC': 0b10000, 'CCCG': 0b10001, 'CCCT': 0b10010, 'CGGG': 0b10011,
    'CGGT': 0b10100, 'CGTT': 0b10101, 'GTTT': 0b10110, 'CTTT': 0b10111,
    'AAAAAAAA': 0b11000, 'CCCCCCCC': 0b11001, 'GGGGGGGG': 0b11010, 'TTTTTTTT': 0b11011,
    'A': 0b11100, 'C': 0b11101, 'G': 0b11110, 'T': 0b11111
}
DNA_DECODING_TABLE = {v: k for k, v in DNA_ENCODING_TABLE.items()}

# Pi Digits Functions
def save_pi_digits(digits: List[int], filename: str = PI_DIGITS_FILE) -> bool:
    try:
        with open(filename, 'w') as f:
            f.write(','.join(str(d) for d in digits))
        logging.info(f"Saved {len(digits)} pi digits to {filename}")
        return True
    except Exception as e:
        logging.error(f"Failed to save pi digits to {filename}: {e}")
        return False

def load_pi_digits(filename: str = PI_DIGITS_FILE, expected_count: int = 3) -> Optional[List[int]]:
    try:
        if not os.path.isfile(filename):
            logging.warning(f"Pi digits file {filename} does not exist")
            return None
        with open(filename, 'r') as f:
            data = f.read().strip()
            if not data:
                logging.warning(f"Pi digits file {filename} is empty")
                return None
            digits = []
            for x in data.split(','):
                if not x.isdigit():
                    logging.warning(f"Invalid integer in {filename}: {x}")
                    return None
                d = int(x)
                if not (0 <= d <= 255):
                    logging.warning(f"Digit out of range in {filename}: {d}")
                    return None
                digits.append(d)
            if len(digits) != expected_count:
                logging.warning(f"Loaded {len(digits)} digits, expected {expected_count}")
                return None
            logging.info(f"Loaded {len(digits)} pi digits from {filename}")
            return digits
    except Exception as e:
        logging.error(f"Failed to load pi digits from {filename}: {e}")
        return None

def generate_pi_digits(num_digits: int = 3, filename: str = PI_DIGITS_FILE) -> List[int]:
    try:
        from mpmath import mp
        mp.dps = num_digits
        pi_digits = [int(d) for d in mp.pi.digits(10)[0]]
        if len(pi_digits) != num_digits:
            logging.error(f"Generated {len(pi_digits)} digits, expected {num_digits}")
            raise ValueError("Incorrect number of pi digits generated")
        mapped_digits = [(d * 255 // 9) % 256 for d in pi_digits]
        save_pi_digits(mapped_digits, filename)
        return mapped_digits
    except ImportError:
        logging.warning("mpmath not installed, using fallback pi digits")
        fallback_digits = [3, 1, 4]
        mapped_fallback = [(d * 255 // 9) % 256 for d in fallback_digits[:num_digits]]
        save_pi_digits(mapped_fallback, filename)
        return mapped_fallback
    except Exception as e:
        logging.error(f"Failed to generate pi digits: {e}")
        fallback_digits = [3, 1, 4]
        mapped_fallback = [(d * 255 // 9) % 256 for d in fallback_digits[:num_digits]]
        save_pi_digits(mapped_fallback, filename)
        return mapped_fallback

PI_DIGITS = generate_pi_digits(3)

# Helper Classes and Functions
class Filetype(Enum):
    DEFAULT = 0
    JPEG = 1
    TEXT = 3

class Node:
    def __init__(self, left=None, right=None, symbol=None):
        self.left = left
        self.right = right
        self.symbol = symbol

    def is_leaf(self):
        return self.left is None and self.right is None

def transform_with_prime_xor_every_3_bytes(data, repeat=100):
    transformed = bytearray(data)
    for prime in PRIMES:
        xor_val = prime if prime == 2 else max(1, math.ceil(prime * 4096 / 28672))
        for _ in range(repeat):
            for i in range(0, len(transformed), 3):
                transformed[i] ^= xor_val
    return bytes(transformed)

def transform_with_pattern_chunk(data, chunk_size=4):
    transformed = bytearray()
    for i in range(0, len(data), chunk_size):
        chunk = data[i:i + chunk_size]
        transformed.extend([b ^ 0xFF for b in chunk])
    return bytes(transformed)

def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n ** 0.5) + 1, 2):
        if n % i == 0:
            return False
    return True

def find_nearest_prime_around(n):
    offset = 0
    while True:
        if is_prime(n - offset):
            return n - offset
        if is_prime(n + offset):
            return n + offset
        offset += 1

# State Table
class StateTable:
    def __init__(self):
        self.table = [
            [1, 2, 0, 0], [3, 5, 1, 0], [4, 6, 0, 1], [7, 10, 2, 0],
            [8, 12, 1, 1], [9, 13, 1, 1], [11, 14, 0, 2], [15, 19, 3, 0],
            [16, 23, 2, 1], [17, 24, 2, 1], [18, 25, 2, 1], [20, 27, 1, 2],
            [21, 28, 1, 2], [22, 29, 1, 2], [26, 30, 0, 3], [31, 33, 4, 0],
            [32, 35, 3, 1], [32, 35, 3, 1], [32, 35, 3, 1], [32, 35, 3, 1],
            [34, 37, 2, 2], [34, 37, 2, 2], [34, 37, 2, 2], [34, 37, 2, 2],
            [34, 37, 2, 2], [34, 37, 2, 2], [36, 39, 1, 3], [36, 39, 1, 3],
            [36, 39, 1, 3], [36, 39, 1, 3], [38, 40, 0, 4], [41, 43, 5, 0],
            [42, 45, 4, 1], [42, 45, 4, 1], [44, 47, 3, 2], [44, 47, 3, 2],
            [46, 49, 2, 3], [46, 49, 2, 3], [48, 51, 1, 4], [48, 51, 1, 4],
            [50, 52, 0, 5], [53, 43, 6, 0], [54, 57, 5, 1], [54, 57, 5, 1],
            [56, 59, 4, 2], [56, 59, 4, 2], [58, 61, 3, 3], [58, 61, 3, 3],
            [60, 63, 2, 4], [60, 63, 2, 4], [62, 65, 1, 5], [62, 65, 1, 5],
            [50, 66, 0, 6], [67, 55, 7, 0], [68, 57, 6, 1], [68, 57, 6, 1],
            [70, 73, 5, 2], [70, 73, 5, 2], [72, 75, 4, 3], [72, 75, 4, 3],
            [74, 77, 3, 4], [74, 77, 3, 4], [76, 79, 2, 5], [76, 79, 2, 5],
            [62, 81, 1, 6], [62, 81, 1, 6], [64, 82, 0, 7], [83, 69, 8, 0],
            [84, 76, 7, 1], [84, 76, 7, 1], [86, 73, 6, 2], [86, 73, 6, 2],
            [44, 59, 5, 3], [44, 59, 5, 3], [58, 61, 4, 4], [58, 61, 4, 4],
            [60, 49, 3, 5], [60, 49, 3, 5], [76, 89, 2, 6], [76, 89, 2, 6],
            [78, 91, 1, 7], [78, 91, 1, 7], [80, 92, 0, 8], [93, 69, 9, 0],
            [94, 87, 8, 1], [94, 87, 8, 1], [96, 45, 7, 2], [96, 45, 7, 2],
            [48, 99, 2, 7], [48, 99, 2, 7], [88, 101, 1, 8], [88, 101, 1, 8],
            [80, 102, 0, 9], [103, 69, 10, 0], [104, 87, 9, 1], [104, 87, 9, 1],
            [106, 57, 8, 2], [106, 57, 8, 2], [62, 109, 2, 8], [62, 109, 2, 8],
            [88, 111, 1, 9], [88, 111, 1, 9], [80, 112, 0, 10], [113, 85, 11, 0],
            [114, 87, 10, 1], [114, 87, 10, 1], [116, 57, 9, 2], [116, 57, 9, 2],
            [62, 119, 2, 9], [62, 119, 2, 9], [88, 121, 1, 10], [88, 121, 1, 10],
            [90, 122, 0, 11], [123, 85, 12, 0], [124, 97, 11, 1], [124, 97, 11, 1],
            [126, 57, 10, 2], [126, 57, 10, 2], [62, 129, 2, 10], [62, 129, 2, 10],
            [98, 131, 1, 11], [98, 131, 1, 11], [90, 132, 0, 12], [133, 85, 13, 0],
            [134, 97, 12, 1], [134, 97, 12, 1], [136, 57, 11, 2], [136, 57, 11, 2],
            [62, 139, 2, 11], [62, 139, 2, 11], [98, 141, 1, 12], [98, 141, 1, 12],
            [90, 142, 0, 13], [143, 95, 14, 0], [144, 97, 13, 1], [144, 97, 13, 1],
            [68, 57, 12, 2], [68, 57, 12, 2], [62, 81, 2, 12], [62, 81, 2, 12],
            [98, 147, 1, 13], [98, 147, 1, 13], [100, 148, 0, 14], [149, 95, 15, 0],
            [150, 107, 14, 1], [150, 107, 14, 1], [108, 151, 1, 14], [108, 151, 1, 14],
            [100, 152, 0, 15], [153, 95, 16, 0], [154, 107, 15, 1], [108, 155, 1, 15],
            [100, 156, 0, 16], [157, 95, 17, 0], [158, 107, 16, 1], [108, 159, 1, 16],
            [100, 160, 0, 17], [161, 105, 18, 0], [162, 107, 17, 1], [108, 163, 1, 17],
            [110, 164, 0, 18], [165, 105, 19, 0], [166, 117, 18, 1], [118, 167, 1, 18],
            [110, 168, 0, 19], [169, 105, 20, 0], [170, 117, 19, 1], [118, 171, 1, 19],
            [110, 172, 0, 20], [173, 105, 21, 0], [174, 117, 20, 1], [118, 175, 1, 20],
            [110, 176, 0, 21], [177, 105, 22, 0], [178, 117, 21, 1], [118, 179, 1, 21],
            [120, 184, 0, 23], [185, 115, 24, 0], [186, 127, 23, 1], [128, 187, 1, 23],
            [120, 188, 0, 24], [189, 115, 25, 0], [190, 127, 24, 1], [128, 191, 1, 24],
            [120, 192, 0, 25], [193, 115, 26, 0], [194, 127, 25, 1], [128, 195, 1, 25],
            [120, 196, 0, 26], [197, 115, 27, 0], [198, 127, 26, 1], [128, 199, 1, 26],
            [120, 200, 0, 27], [201, 115, 28, 0], [202, 127, 27, 1], [128, 203, 1, 27],
            [120, 204, 0, 28], [205, 115, 29, 0], [206, 127, 28, 1], [128, 207, 1, 28],
            [120, 208, 0, 29], [209, 125, 30, 0], [210, 127, 29, 1], [128, 211, 1, 29],
            [130, 212, 0, 30], [213, 125, 31, 0], [214, 137, 30, 1], [138, 215, 1, 30],
            [130, 216, 0, 31], [217, 125, 32, 0], [218, 137, 31, 1], [138, 219, 1, 31],
            [130, 220, 0, 32], [221, 125, 33, 0], [222, 137, 32, 1], [138, 223, 1, 32],
            [130, 224, 0, 33], [225, 125, 34, 0], [226, 137, 33, 1], [138, 227, 1, 33],
            [130, 228, 0, 34], [229, 125, 35, 0], [230, 137, 34, 1], [138, 231, 1, 34],
            [130, 232, 0, 35], [233, 125, 36, 0], [234, 137, 35, 1], [138, 235, 1, 35],
            [130, 236, 0, 36], [237, 125, 37, 0], [238, 137, 36, 1], [138, 239, 1, 36],
            [130, 240, 0, 37], [241, 125, 38, 0], [242, 137, 37, 1], [138, 243, 1, 37],
            [130, 244, 0, 38], [245, 135, 39, 0], [246, 137, 38, 1], [138, 247, 1, 38],
            [140, 248, 0, 39], [249, 135, 40, 0], [250, 69, 39, 1], [80, 251, 1, 39],
            [140, 252, 0, 40], [249, 135, 41, 0], [250, 69, 40, 1], [80, 251, 1, 40],
            [140, 252, 0, 41]
        ]

# Smart Compressor
class SmartCompressor:
    def __init__(self):
        self.dictionaries = self.load_dictionaries()

    def load_dictionaries(self):
        data = []
        for filename in DICTIONARY_FILES:
            if os.path.exists(filename):
                try:
                    with open(filename, "r", encoding="utf-8", errors="ignore") as f:
                        data.append(f.read())
                    logging.info(f"Loaded dictionary: {filename}")
                except Exception as e:
                    logging.warning(f"Could not read {filename}: {e}")
            else:
                logging.warning(f"Missing dictionary: {filename}")
        return data

    def compute_sha256(self, data):
        return hashlib.sha256(data).hexdigest()

    def compute_sha256_binary(self, data):
        return hashlib.sha256(data).digest()

    def find_hash_in_dictionaries(self, hash_hex):
        for filename in DICTIONARY_FILES:
            if not os.path.exists(filename):
                continue
            try:
                with open(filename, "r", encoding="utf-8", errors="ignore") as f:
                    for line in f:
                        if hash_hex in line:
                            logging.info(f"Hash {hash_hex[:16]}... found in {filename}")
                            return filename
            except Exception as e:
                logging.warning(f"Error searching {filename}: {e}")
        return None

    def generate_8byte_sha(self, data):
        try:
            return hashlib.sha256(data).digest()[:8]
        except Exception as e:
            logging.error(f"Failed to generate SHA: {e}")
            return None

    def paq_compress(self, data):
        if not data:
            logging.warning("paq_compress: Empty input, returning empty bytes")
            return b''
        try:
            if isinstance(data, bytearray):
                data = bytes(data)
            elif not isinstance(data, bytes):
                raise TypeError(f"Expected bytes or bytearray, got {type(data)}")
            compressed = paq.compress(data)
            logging.info("PAQ9a compression complete")
            return compressed
        except Exception as e:
            logging.error(f"PAQ9a compression failed: {e}")
            return None

    def paq_decompress(self, data):
        if not data:
            logging.warning("paq_decompress: Empty input, returning empty bytes")
            return b''
        try:
            decompressed = paq.decompress(data)
            logging.info("PAQ9a decompression complete")
            return decompressed
        except Exception as e:
            logging.error(f"PAQ9a decompression failed: {e}")
            return None

    def reversible_transform(self, data):
        logging.info("Applying XOR transform (0xAA)")
        transformed = bytes(b ^ 0xAA for b in data)
        logging.info("XOR transform complete")
        return transformed

    def reverse_reversible_transform(self, data):
        logging.info("Reversing XOR transform (0xAA)")
        return self.reversible_transform(data)

    def compress(self, input_data, input_file):
        if not input_data:
            logging.warning("Empty input, returning minimal output")
            return bytes([0])

        original_hash = self.compute_sha256(input_data)
        logging.info(f"SHA-256 of input: {original_hash[:16]}...")

        found = self.find_hash_in_dictionaries(original_hash)
        if found:
            logging.info(f"Hash found in dictionary: {found}")
        else:
            logging.info("Hash not found, proceeding with compression")

        if input_file.endswith(".paq") and any(x in input_file for x in ["words", "lines", "sentence"]):
            sha = self.generate_8byte_sha(input_data)
            if sha and len(input_data) > 8:
                logging.info(f"SHA-8 for .paq file: {sha.hex()}")
                return sha
            logging.info("Original smaller than SHA, skipping compression")
            return None

        transformed = self.reversible_transform(input_data)
        compressed = self.paq_compress(transformed)
        if compressed is None:
            logging.error("Compression failed")
            return None

        if len(compressed) < len(input_data):
            output = self.compute_sha256_binary(input_data) + compressed
            logging.info(f"Smart compression: Original {len(input_data)} bytes, Compressed {len(compressed)} bytes")
            return output
        else:
            logging.info("Compression not efficient, returning None")
            return None

    def decompress(self, input_data):
        if len(input_data) < 32:
            logging.error("Input too short for Smart Compressor")
            return None

        stored_hash = input_data[:32]
        compressed_data = input_data[32:]

        decompressed = self.paq_decompress(compressed_data)
        if decompressed is None:
            return None

        original = self.reverse_reversible_transform(decompressed)
        computed_hash = self.compute_sha256_binary(original)
        if computed_hash == stored_hash:
            logging.info("Hash verification successful")
            return original
        else:
            logging.error("Hash verification failed")
            return None

# PAQJP Compressor
class PAQJPCompressor:
    def __init__(self):
        self.PI_DIGITS = PI_DIGITS
        self.PRIMES = PRIMES
        self.seed_tables = self.generate_seed_tables()
        self.SQUARE_OF_ROOT = 2
        self.ADD_NUMBERS = 1
        self.MULTIPLY = 3
        self.fibonacci = self.generate_fibonacci(100)
        self.state_table = StateTable()

    def generate_fibonacci(self, n: int) -> List[int]:
        fib = [0, 1]
        for i in range(2, n):
            fib.append(fib[i-1] + fib[i-2])
        return fib

    def generate_seed_tables(self, num_tables=126, table_size=256, min_val=5, max_val=255, seed=42):
        random.seed(seed)
        return [[random.randint(min_val, max_val) for _ in range(table_size)] for _ in range(num_tables)]

    def get_seed(self, table_idx: int, value: int) -> int:
        if 0 <= table_idx < len(self.seed_tables):
            return self.seed_tables[table_idx][value % len(self.seed_tables[table_idx])]
        return 0

    def create_quantum_transform_circuit(self, transform_idx: int, data_length: int) -> qiskit.QuantumCircuit:
        circuit = qiskit.QuantumCircuit(9)
        for i in range(9):
            circuit.h(i)
        theta = (transform_idx * data_length) % 512 / 512 * math.pi
        for i in range(9):
            circuit.ry(theta, i)
        for i in range(8):
            circuit.cx(i, i + 1)
        logging.info(f"Defined quantum circuit for transform {transform_idx}, theta={theta:.2f}")
        return circuit

    def calculate_frequencies(self, binary_str):
        if not binary_str:
            logging.warning("Empty binary string, returning empty frequencies")
            return {}
        frequencies = {}
        for bit in binary_str:
            frequencies[bit] = frequencies.get(bit, 0) + 1
        return frequencies

    def build_huffman_tree(self, frequencies):
        if not frequencies:
            logging.warning("No frequencies, returning None")
            return None
        heap = [(freq, Node(symbol=symbol)) for symbol, freq in frequencies.items()]
        heapq.heapify(heap)
        while len(heap) > 1:
            freq1, node1 = heapq.heappop(heap)
            freq2, node2 = heapq.heappop(heap)
            new_node = Node(left=node1, right=node2)
            heapq.heappush(heap, (freq1 + freq2, new_node))
        return heap[0][1]

    def generate_huffman_codes(self, root, current_code="", codes={}):
        if root is None:
            logging.warning("Huffman tree is None, returning empty codes")
            return {}
        if root.is_leaf():
            codes[root.symbol] = current_code or "0"
            return codes
        if root.left:
            self.generate_huffman_codes(root.left, current_code + "0", codes)
        if root.right:
            self.generate_huffman_codes(root.right, current_code + "1", codes)
        return codes

    def compress_data_huffman(self, binary_str):
        if not binary_str:
            logging.warning("Empty binary string, returning empty compressed string")
            return ""
        frequencies = self.calculate_frequencies(binary_str)
        huffman_tree = self.build_huffman_tree(frequencies)
        if huffman_tree is None:
            return ""
        huffman_codes = self.generate_huffman_codes(huffman_tree)
        if '0' not in huffman_codes:
            huffman_codes['0'] = '0'
        if '1' not in huffman_codes:
            huffman_codes['1'] = '1'
        return ''.join(huffman_codes[bit] for bit in binary_str)

    def decompress_data_huffman(self, compressed_str):
        if not compressed_str:
            logging.warning("Empty compressed string, returning empty decompressed string")
            return ""
        frequencies = self.calculate_frequencies(compressed_str)
        huffman_tree = self.build_huffman_tree(frequencies)
        if huffman_tree is None:
            return ""
        huffman_codes = self.generate_huffman_codes(huffman_tree)
        reversed_codes = {code: symbol for symbol, code in huffman_codes.items()}
        decompressed_str = ""
        current_code = ""
        for bit in compressed_str:
            current_code += bit
            if current_code in reversed_codes:
                decompressed_str += reversed_codes[current_code]
                current_code = ""
        return decompressed_str

    def paq_compress(self, data):
        if not data:
            logging.warning("paq_compress: Empty input, returning empty bytes")
            return b''
        try:
            if isinstance(data, bytearray):
                data = bytes(data)
            elif not isinstance(data, bytes):
                raise TypeError(f"Expected bytes or bytearray, got {type(data)}")
            compressed = paq.compress(data)
            logging.info("PAQ9a compression complete")
            return compressed
        except Exception as e:
            logging.error(f"PAQ9a compression failed: {e}")
            return None

    def paq_decompress(self, data):
        if not data:
            logging.warning("paq_decompress: Empty input, returning empty bytes")
            return b''
        try:
            decompressed = paq.decompress(data)
            logging.info("PAQ9a decompression complete")
            return decompressed
        except Exception as e:
            logging.error(f"PAQ9a decompression failed: {e}")
            return None

    def transform_genomecompress(self, data: bytes) -> bytes:
        if not data:
            logging.warning("transform_genomecompress: Empty input, returning empty bytes")
            return b''
        try:
            dna_str = data.decode('ascii').upper()
            if not all(c in 'ACGT' for c in dna_str):
                logging.error("transform_genomecompress: Invalid DNA sequence")
                return b''
        except Exception as e:
            logging.error(f"transform_genomecompress: Failed to decode: {e}")
            return b''
        n = len(dna_str)
        r = n % 4
        output_bits = []
        i = 0
        while i < n - r:
            if i + 8 <= n and dna_str[i:i+8] in DNA_ENCODING_TABLE:
                segment = dna_str[i:i+8]
                output_bits.extend([int(b) for b in format(DNA_ENCODING_TABLE[segment], '05b')])
                i += 8
            else:
                segment = dna_str[i:i+4]
                if segment in DNA_ENCODING_TABLE:
                    output_bits.extend([int(b) for b in format(DNA_ENCODING_TABLE[segment], '05b')])
                    i += 4
                else:
                    logging.error(f"transform_genomecompress: Invalid segment at {i}: {segment}")
                    return b''
        for j in range(i, n):
            segment = dna_str[j]
            output_bits.extend([int(b) for b in format(DNA_ENCODING_TABLE[segment], '05b')])
        bit_str = ''.join(map(str, output_bits))
        byte_length = (len(bit_str) + 7) // 8
        byte_data = int(bit_str, 2).to_bytes(byte_length, 'big') if bit_str else b''
        logging.info(f"transform_genomecompress: Encoded {n} bases to {len(byte_data)} bytes")
        return byte_data

    def reverse_transform_genomecompress(self, data: bytes) -> bytes:
        if not data:
            logging.warning("reverse_transform_genomecompress: Empty input")
            return b''
        bit_str = bin(int.from_bytes(data, 'big'))[2:].zfill(len(data) * 8)
        output = []
        i = 0
        while i < len(bit_str):
            if i + 5 > len(bit_str):
                logging.warning(f"reverse_transform_genomecompress: Incomplete segment at {i}")
                break
            segment_bits = bit_str[i:i+5]
            segment_val = int(segment_bits, 2)
            if segment_val not in DNA_DECODING_TABLE:
                logging.error(f"reverse_transform_genomecompress: Invalid code: {segment_bits}")
                return b''
            output.append(DNA_DECODING_TABLE[segment_val])
            i += 5
        dna_str = ''.join(output)
        result = dna_str.encode('ascii')
        logging.info(f"reverse_transform_genomecompress: Decoded {len(result)} bases")
        return result

    def transform_01(self, data, repeat=100):
        if not data:
            logging.warning("transform_01: Empty input, returning empty bytes")
            return b''
        return transform_with_prime_xor_every_3_bytes(data, repeat=repeat)

    def reverse_transform_01(self, data, repeat=100):
        return self.transform_01(data, repeat=repeat)

    def transform_03(self, data):
        if not data:
            logging.warning("transform_03: Empty input, returning empty bytes")
            return b''
        return transform_with_pattern_chunk(data)

    def reverse_transform_03(self, data):
        return self.transform_03(data)

    def transform_04(self, data, repeat=100):
        if not data:
            logging.warning("transform_04: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        for _ in range(repeat):
            for i in range(len(transformed)):
                transformed[i] = (transformed[i] - (i % 256)) % 256
        return bytes(transformed)

    def reverse_transform_04(self, data, repeat=100):
        if not data:
            logging.warning("reverse_transform_04: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        for _ in range(repeat):
            for i in range(len(transformed)):
                transformed[i] = (transformed[i] + (i % 256)) % 256
        return bytes(transformed)

    def transform_05(self, data, shift=3):
        if not data:
            logging.warning("transform_05: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        for i in range(len(transformed)):
            transformed[i] = ((transformed[i] << shift) | (transformed[i] >> (8 - shift))) & 0xFF
        return bytes(transformed)

    def reverse_transform_05(self, data, shift=3):
        if not data:
            logging.warning("reverse_transform_05: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        for i in range(len(transformed)):
            transformed[i] = ((transformed[i] >> shift) | (transformed[i] << (8 - shift))) & 0xFF
        return bytes(transformed)

    def transform_06(self, data, seed=42):
        if not data:
            logging.warning("transform_06: Empty input, returning empty bytes")
            return b''
        random.seed(seed)
        substitution = list(range(256))
        random.shuffle(substitution)
        transformed = bytearray(data)
        for i in range(len(transformed)):
            transformed[i] = substitution[transformed[i]]
        return bytes(transformed)

    def reverse_transform_06(self, data, seed=42):
        if not data:
            logging.warning("reverse_transform_06: Empty input, returning empty bytes")
            return b''
        random.seed(seed)
        substitution = list(range(256))
        random.shuffle(substitution)
        reverse_substitution = [0] * 256
        for i, v in enumerate(substitution):
            reverse_substitution[v] = i
        transformed = bytearray(data)
        for i in range(len(transformed)):
            transformed[i] = reverse_substitution[transformed[i]]
        return bytes(transformed)

    def transform_07(self, data, repeat=100):
        if not data:
            logging.warning("transform_07: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        pi_length = len(self.PI_DIGITS)
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"transform_07: {cycles} cycles for {len(data)} bytes")
        shift = len(data) % pi_length
        self.PI_DIGITS = self.PI_DIGITS[shift:] + self.PI_DIGITS[:shift]
        size_byte = len(data) % 256
        for i in range(len(transformed)):
            transformed[i] ^= size_byte
        for _ in range(cycles * repeat // 10):
            for i in range(len(transformed)):
                pi_digit = self.PI_DIGITS[i % pi_length]
                transformed[i] ^= pi_digit
        return bytes(transformed)

    def reverse_transform_07(self, data, repeat=100):
        if not data:
            logging.warning("reverse_transform_07: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        pi_length = len(self.PI_DIGITS)
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"reverse_transform_07: {cycles} cycles for {len(data)} bytes")
        for _ in range(cycles * repeat // 10):
            for i in range(len(transformed)):
                pi_digit = self.PI_DIGITS[i % pi_length]
                transformed[i] ^= pi_digit
        size_byte = len(data) % 256
        for i in range(len(transformed)):
            transformed[i] ^= size_byte
        shift = len(data) % pi_length
        self.PI_DIGITS = self.PI_DIGITS[-shift:] + self.PI_DIGITS[:-shift]
        return bytes(transformed)

    def transform_08(self, data, repeat=100):
        if not data:
            logging.warning("transform_08: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        pi_length = len(self.PI_DIGITS)
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"transform_08: {cycles} cycles for {len(data)} bytes")
        shift = len(data) % pi_length
        self.PI_DIGITS = self.PI_DIGITS[shift:] + self.PI_DIGITS[:shift]
        size_prime = find_nearest_prime_around(len(data) % 256)
        for i in range(len(transformed)):
            transformed[i] ^= size_prime
        for _ in range(cycles * repeat // 10):
            for i in range(len(transformed)):
                pi_digit = self.PI_DIGITS[i % pi_length]
                transformed[i] ^= pi_digit
        return bytes(transformed)

    def reverse_transform_08(self, data, repeat=100):
        if not data:
            logging.warning("reverse_transform_08: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        pi_length = len(self.PI_DIGITS)
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"reverse_transform_08: {cycles} cycles for {len(data)} bytes")
        for _ in range(cycles * repeat // 10):
            for i in range(len(transformed)):
                pi_digit = self.PI_DIGITS[i % pi_length]
                transformed[i] ^= pi_digit
        size_prime = find_nearest_prime_around(len(data) % 256)
        for i in range(len(transformed)):
            transformed[i] ^= size_prime
        shift = len(data) % pi_length
        self.PI_DIGITS = self.PI_DIGITS[-shift:] + self.PI_DIGITS[:-shift]
        return bytes(transformed)

    def transform_09(self, data, repeat=100):
        if not data:
            logging.warning("transform_09: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        pi_length = len(self.PI_DIGITS)
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"transform_09: {cycles} cycles, {repeat} repeats for {len(data)} bytes")
        shift = len(data) % pi_length
        self.PI_DIGITS = self.PI_DIGITS[shift:] + self.PI_DIGITS[:shift]
        size_prime = find_nearest_prime_around(len(data) % 256)
        seed_idx = len(data) % len(self.seed_tables)
        seed_value = self.get_seed(seed_idx, len(data))
        for i in range(len(transformed)):
            transformed[i] ^= size_prime ^ seed_value
        for _ in range(cycles * repeat // 10):
            for i in range(len(transformed)):
                pi_digit = self.PI_DIGITS[i % pi_length]
                transformed[i] ^= pi_digit ^ (i % 256)
        return bytes(transformed)

    def reverse_transform_09(self, data, repeat=100):
        if not data:
            logging.warning("reverse_transform_09: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        pi_length = len(self.PI_DIGITS)
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"reverse_transform_09: {cycles} cycles, {repeat} repeats for {len(data)} bytes")
        for _ in range(cycles * repeat // 10):
            for i in range(len(transformed)):
                pi_digit = self.PI_DIGITS[i % pi_length]
                transformed[i] ^= pi_digit ^ (i % 256)
        size_prime = find_nearest_prime_around(len(data) % 256)
        seed_idx = len(data) % len(self.seed_tables)
        seed_value = self.get_seed(seed_idx, len(data))
        for i in range(len(transformed)):
            transformed[i] ^= size_prime ^ seed_value
        shift = len(data) % pi_length
        self.PI_DIGITS = self.PI_DIGITS[-shift:] + self.PI_DIGITS[:-shift]
        return bytes(transformed)

    def transform_10(self, data, repeat=100):
        if not data:
            logging.warning("transform_10: Empty input, returning empty bytes with n=0")
            return bytes([0])
        transformed = bytearray(data)
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"transform_10: {cycles} cycles, {repeat} repeats for {len(data)} bytes")
        count = 0
        for i in range(len(data) - 1):
            if data[i] == 0x58 and data[i + 1] == 0x31:
                count += 1
        logging.info(f"transform_10: Found {count} 'X1' sequences")
        n = (((count * self.SQUARE_OF_ROOT) + self.ADD_NUMBERS) // 3) * self.MULTIPLY
        n = n % 256
        logging.info(f"transform_10: Computed n = {n}")
        for _ in range(cycles * repeat // 10):
            for i in range(len(transformed)):
                transformed[i] ^= n
        return bytes([n]) + bytes(transformed)

    def reverse_transform_10(self, data, repeat=100):
        if len(data) < 1:
            logging.warning("reverse_transform_10: Data too short, returning empty bytes")
            return b''
        n = data[0]
        transformed = bytearray(data[1:])
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"reverse_transform_10: {cycles} cycles, {repeat} repeats, n={n}")
        for _ in range(cycles * repeat // 10):
            for i in range(len(transformed)):
                transformed[i] ^= n
        return bytes(transformed)

    def transform_11(self, data, repeat=100):
        if not data:
            logging.warning("transform_11: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        total_cycles = cycles * repeat // 10
        logging.info(f"transform_11: {cycles} cycles, {repeat} repeats, total {total_cycles} for {len(data)} bytes")
        
        # Step 1: Apply Algorithm 54 (single-seed XOR)
        seed_idx = 54 % len(self.seed_tables)  # 54 % 126 = 54
        seed_value = self.get_seed(seed_idx, len(data))  # seed_tables[54][len(data) % 256]
        logging.info(f"transform_11: Applying Algorithm 54 with seed {seed_value} for seed_idx {seed_idx}")
        for i in range(len(transformed)):
            transformed[i] ^= seed_value
        
        # Step 2: Subtract seed_value and apply XOR with 3-byte word from SHA-256 hex
        sha_hash_hex = hashlib.sha256(data).hexdigest()[:6]  # First 6 hex chars (3 bytes)
        try:
            sha_word = bytes.fromhex(sha_hash_hex)
        except ValueError as e:
            logging.error(f"transform_11: Invalid hex string {sha_hash_hex}: {e}")
            return b''
        logging.info(f"transform_11: Using SHA-256 first 6 hex chars as 3-byte word: {sha_word.hex()}")
        for i in range(len(transformed)):
            transformed[i] = (transformed[i] - seed_value) % 256  # Subtract seed_value
        for _ in range(total_cycles):
            for i in range(len(transformed)):
                hash_byte = sha_word[i % 3]
                transformed[i] ^= hash_byte
        
        # Prepend 3 bytes for total_cycles
        cycle_bytes = total_cycles.to_bytes(3, 'big')
        return cycle_bytes + bytes(transformed)

    def reverse_transform_11(self, data, original_data=None, repeat=100):
        if len(data) < 3:
            logging.warning("reverse_transform_11: Data too short, need at least 3 bytes for cycle count")
            return b''
        # Read the cycle count
        total_cycles = int.from_bytes(data[:3], 'big')
        transformed = bytearray(data[3:])
        data_size_kb = len(data) / 1024
        cycles = min(10, max(1, int(data_size_kb)))
        logging.info(f"reverse_transform_11: {cycles} cycles, {repeat} repeats, total {total_cycles} for {len(data)} bytes")
        
        # Step 1: Reverse the SHA-256 XOR
        if original_data is None:
            logging.warning("reverse_transform_11: No original data provided, using placeholder")
            return bytes(transformed)
        sha_hash_hex = hashlib.sha256(original_data).hexdigest()[:6]
        try:
            sha_word = bytes.fromhex(sha_hash_hex)
        except ValueError as e:
            logging.error(f"reverse_transform_11: Invalid hex string {sha_hash_hex}: {e}")
            return b''
        logging.info(f"reverse_transform_11: Using SHA-256 first 6 hex chars as 3-byte word: {sha_word.hex()}")
        for _ in range(total_cycles):
            for i in range(len(transformed)):
                hash_byte = sha_word[i % 3]
                transformed[i] ^= hash_byte
        
        # Step 2: Add back the seed_value (reverse subtraction) and reverse Algorithm 54
        seed_idx = 54 % len(self.seed_tables)  # 54 % 126 = 54
        seed_value = self.get_seed(seed_idx, len(data))
        logging.info(f"reverse_transform_11: Reversing Algorithm 54 with seed {seed_value} for seed_idx {seed_idx}")
        for i in range(len(transformed)):
            transformed[i] = (transformed[i] + seed_value) % 256  # Reverse subtraction
            transformed[i] ^= seed_value  # Reverse Algorithm 54 XOR
        
        return bytes(transformed)

    def transform_12(self, data, repeat=100):
        if not data:
            logging.warning("transform_12: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        data_size = len(data)
        fib_length = len(self.fibonacci)
        logging.info(f"transform_12: Fibonacci transform for {data_size} bytes, repeat={repeat}")
        for _ in range(repeat):
            for i in range(len(transformed)):
                fib_index = i % fib_length
                fib_value = self.fibonacci[fib_index] % 256
                transformed[i] ^= fib_value
        return bytes(transformed)

    def reverse_transform_12(self, data, repeat=100):
        if not data:
            logging.warning("reverse_transform_12: Empty input, returning empty bytes")
            return b''
        transformed = bytearray(data)
        data_size = len(data)
        fib_length = len(self.fibonacci)
        logging.info(f"reverse_transform_12: Reversing Fibonacci for {data_size} bytes, repeat={repeat}")
        for _ in range(repeat):
            for i in range(len(transformed)):
                fib_index = i % fib_length
                fib_value = self.fibonacci[fib_index] % 256
                transformed[i] ^= fib_value
        return bytes(transformed)

    def generate_transform_method(self, n):
        self.create_quantum_transform_circuit(n, 1048576)
        def transform(data, repeat=100):
            if not data:
                logging.warning(f"transform_{n}: Empty input, returning empty bytes")
                return b''
            transformed = bytearray(data)
            seed_idx = n % len(self.seed_tables)
            seed_value = self.get_seed(seed_idx, len(data))
            logging.info(f"transform_{n}: Using seed {seed_value} for seed_idx {seed_idx}")
            for i in range(len(transformed)):
                transformed[i] ^= seed_value
            return bytes(transformed)

        def reverse_transform(data, repeat=100):
            return transform(data, repeat)

        return transform, reverse_transform

    def compress_with_best_method(self, data, filetype, input_filename, mode="slow"):
        if not data:
            logging.warning("compress_with_best_method: Empty input, returning minimal marker")
            return bytes([0])

        is_dna = False
        try:
            data_str = data.decode('ascii').upper()
            is_dna = all(c in 'ACGT' for c in data_str)
        except:
            pass

        fast_transformations = [
            (1, self.transform_04),
            (2, self.transform_01),
            (3, self.transform_03),
            (5, self.transform_05),
            (6, self.transform_06),
            (7, self.transform_07),
            (8, self.transform_08),
            (9, self.transform_09),
            (11, self.transform_11),
            (12, self.transform_12),
        ]
        slow_transformations = fast_transformations + [
            (10, self.transform_10),
        ] + [(i, self.generate_transform_method(i)[0]) for i in range(16, 256)]

        if is_dna:
            transformations = [(0, self.transform_genomecompress)] + slow_transformations
        else:
            transformations = slow_transformations if mode == "slow" else fast_transformations

        if filetype in [Filetype.JPEG, Filetype.TEXT]:
            prioritized = [
                (7, self.transform_07),
                (8, self.transform_08),
                (9, self.transform_09),
                (11, self.transform_11),
                (12, self.transform_12),
            ]
            if is_dna:
                prioritized = [(0, self.transform_genomecompress)] + prioritized
            if mode == "slow":
                prioritized += [(10, self.transform_10)] + \
                              [(i, self.generate_transform_method(i)[0]) for i in range(16, 256)]
            transformations = prioritized + [t for t in transformations if t[0] not in [0, 7, 8, 9, 10, 11, 12] + list(range(16, 256))]

        methods = [('paq', self.paq_compress)]
        best_compressed = None
        best_size = float('inf')
        best_marker = None
        best_method = None

        # Precompute for transform_11
        sha_hash_hex_11 = hashlib.sha256(data).hexdigest()[:6]
        try:
            sha_word_11 = bytes.fromhex(sha_hash_hex_11)
        except ValueError:
            sha_word_11 = None
        seed_idx_54 = 54 % len(self.seed_tables)
        seed_value_54 = self.get_seed(seed_idx_54, len(data))

        for marker, transform in transformations:
            # Special handling for transform_11 to ensure reversibility
            if marker == 11 and sha_word_11:
                transformed = self.transform_11(data)
                # Verify losslessness
                reversed_data = bytearray(transformed[3:])  # Skip 3-byte cycle count
                # Reverse Algorithm 11
                for _ in range(min(10, max(1, int(len(data) / 1024))) * 100 // 10):
                    for i in range(len(reversed_data)):
                        reversed_data[i] ^= sha_word_11[i % 3]
                # Reverse subtraction and Algorithm 54
                for i in range(len(reversed_data)):
                    reversed_data[i] = (reversed_data[i] + seed_value_54) % 256
                    reversed_data[i] ^= seed_value_54
                if bytes(reversed_data) != data:
                    logging.warning(f"transform_11 not lossless, skipping")
                    continue
            else:
                transformed = transform(data)
            
            for method_name, compress_func in methods:
                try:
                    compressed = compress_func(transformed)
                    if compressed is None:
                        continue
                    size = len(compressed)
                    if marker == 11:
                        size += 3  # Account for cycle count bytes
                    logging.info(f"Tested marker {marker}, method {method_name}, size {size} bytes")
                    if size < best_size:
                        best_size = size
                        best_compressed = compressed
                        best_marker = marker
                        best_method = method_name
                except Exception as e:
                    logging.warning(f"Compression method {method_name} with transform {marker} failed: {e}")
                    continue

        if len(data) < HUFFMAN_THRESHOLD:
            binary_str = bin(int(binascii.hexlify(data), 16))[2:].zfill(len(data) * 8)
            compressed_huffman = self.compress_data_huffman(binary_str)
            compressed_bytes = int(compressed_huffman, 2).to_bytes((len(compressed_huffman) + 7) // 8, 'big') if compressed_huffman else b''
            if compressed_bytes and len(compressed_bytes) < best_size:
                best_size = len(compressed_bytes)
                best_compressed = compressed_bytes
                best_marker = 4
                best_method = 'huffman'
                logging.info(f"Huffman better, marker 4, size {best_size} bytes")

        if best_compressed is None:
            logging.error("All compression methods failed, returning original with marker 0")
            return bytes([0]) + data

        logging.info(f"Best method: {best_method}, Marker: {best_marker}, Size: {best_size + 1} bytes for {filetype.name} in {mode} mode")
        return bytes([best_marker]) + best_compressed

    def decompress_with_best_method(self, data):
        if len(data) < 1:
            logging.warning("decompress_with_best_method: Insufficient data")
            return b'', None

        method_marker = data[0]
        compressed_data = data[1:]

        reverse_transforms = {
            0: self.reverse_transform_genomecompress,
            1: self.reverse_transform_04,
            2: self.reverse_transform_01,
            3: self.reverse_transform_03,
            5: self.reverse_transform_05,
            6: self.reverse_transform_06,
            7: self.reverse_transform_07,
            8: self.reverse_transform_08,
            9: self.reverse_transform_09,
            10: self.reverse_transform_10,
            11: self.reverse_transform_11,
            12: self.reverse_transform_12,
        }
        reverse_transforms.update({i: self.generate_transform_method(i)[1] for i in range(16, 256)})

        if method_marker == 4:
            binary_str = bin(int(binascii.hexlify(compressed_data), 16))[2:].zfill(len(compressed_data) * 8)
            decompressed_binary = self.decompress_data_huffman(binary_str)
            if not decompressed_binary:
                logging.warning("Huffman decompression empty")
                return b'', None
            try:
                num_bytes = (len(decompressed_binary) + 7) // 8
                hex_str = "%0*x" % (num_bytes * 2, int(decompressed_binary, 2))
                if len(hex_str) % 2 != 0:
                    hex_str = '0' + hex_str
                return binascii.unhexlify(hex_str), None
            except Exception as e:
                logging.error(f"Huffman data conversion failed: {e}")
                return b'', None

        if method_marker not in reverse_transforms:
            logging.error(f"Unknown marker: {method_marker}")
            return b'', None

        try:
            decompressed = self.paq_decompress(compressed_data)
            if not decompressed:
                logging.warning("PAQ decompression empty")
                return b'', None
            if method_marker == 11:
                # For transform_11, iterate to find original data
                result = bytearray(decompressed)
                # Try possible original data by reversing transform
                for _ in range(10):  # Max attempts to find correct original
                    temp = bytearray(result)
                    # Reverse Algorithm 11
                    sha_hash_hex = hashlib.sha256(temp).hexdigest()[:6]
                    sha_word = bytes.fromhex(sha_hash_hex)
                    for _ in range(int.from_bytes(decompressed[:3], 'big')):
                        for i in range(len(temp)):
                            temp[i] ^= sha_word[i % 3]
                    # Reverse subtraction and Algorithm 54
                    seed_idx = 54 % len(self.seed_tables)
                    seed_value = self.get_seed(seed_idx, len(decompressed))
                    for i in range(len(temp)):
                        temp[i] = (temp[i] + seed_value) % 256
                        temp[i] ^= seed_value
                    # Verify by applying forward transform
                    verify = bytearray(temp)
                    # Apply Algorithm 54
                    for i in range(len(verify)):
                        verify[i] ^= seed_value
                    # Apply subtraction and SHA-256 XOR
                    verify_sha = hashlib.sha256(temp).hexdigest()[:6]
                    verify_word = bytes.fromhex(verify_sha)
                    for i in range(len(verify)):
                        verify[i] = (verify[i] - seed_value) % 256
                    for _ in range(int.from_bytes(decompressed[:3], 'big')):
                        for i in range(len(verify)):
                            verify[i] ^= verify_word[i % 3]
                    if verify == decompressed[3:]:  # Skip cycle count bytes
                        logging.info(f"transform_11 decompression verified")
                        return bytes(temp), method_marker
                    result = temp  # Try next iteration
                logging.error(f"transform_11 decompression verification failed")
                return b'', None
            else:
                result = reverse_transforms[method_marker](decompressed)
                zero_count = sum(1 for b in result if b == 0)
                logging.info(f"Decompressed with marker {method_marker}, {zero_count} zeros")
                return result, method_marker
        except Exception as e:
            logging.error(f"Decompression failed for marker {method_marker}: {e}")
            return b'', None

    def compress(self, input_file: str, output_file: str, filetype: Filetype = Filetype.DEFAULT, mode: str = "slow") -> bool:
        try:
            with open(input_file, 'rb') as f:
                data = f.read()
            if not data:
                logging.warning(f"Input file {input_file} is empty")
                return False
            compressed = self.compress_with_best_method(data, filetype, input_file, mode)
            with open(output_file, 'wb') as f:
                f.write(compressed)
            logging.info(f"Compressed {input_file} to {output_file}, size {len(compressed)} bytes")
            return True
        except Exception as e:
            logging.error(f"Compression failed for {input_file}: {e}")
            return False

    def decompress(self, input_file: str, output_file: str) -> bool:
        try:
            with open(input_file, 'rb') as f:
                data = f.read()
            if not data:
                logging.warning(f"Input file {input_file} is empty")
                return False
            decompressed, marker = self.decompress_with_best_method(data)
            if not decompressed:
                logging.error(f"Decompression failed for {input_file}")
                return False
            with open(output_file, 'wb') as f:
                f.write(decompressed)
            logging.info(f"Decompressed {input_file} to {output_file}, size {len(decompressed)} bytes, marker {marker}")
            return True
        except Exception as e:
            logging.error(f"Decompression failed for {input_file}: {e}")
            return False

# Main Function
def detect_filetype(filename: str) -> Filetype:
    _, ext = os.path.splitext(filename.lower())
    if ext in ['.jpg', '.jpeg']:
        return Filetype.JPEG
    elif ext in ['.txt', '.dna']:
        try:
            with open(filename, 'r', encoding='ascii') as f:
                sample = f.read(1000)
                if all(c in 'ACGTacgt\n' for c in sample):
                    return Filetype.TEXT
        except:
            pass
        return Filetype.TEXT
    else:
        return Filetype.DEFAULT

def main():
    print("PAQJP_6.7 Compression System")
    print("Created by Jurijus Pacalovas")
    print("Options:")
    print("1 - Compress file (Best of Smart Compressor [00] or PAQJP_6 [01])")
    print("2 - Decompress file")

    compressor = PAQJPCompressor()

    try:
        choice = input("Enter 1 or 2: ").strip()
        if choice not in ('1', '2'):
            print("Invalid choice. Exiting.")
            return
    except (EOFError, KeyboardInterrupt):
        print("Program terminated by user")
        return

    mode = "slow"
    if choice == '1':
        try:
            mode_choice = input("Enter compression mode (1 for fast, 2 for slow): ").strip()
            if mode_choice == '1':
                mode = "fast"
            elif mode_choice == '2':
                mode = "slow"
            else:
                print("Invalid mode, defaulting to slow")
                mode = "slow"
        except (EOFError, KeyboardInterrupt):
            print("Defaulting to slow mode")
            mode = "slow"

        input_file = input("Enter input file path: ").strip()
        output_file = input("Enter output file path: ").strip()

        if not os.path.exists(input_file):
            print(f"Input file {input_file} not found")
            return
        if not os.access(input_file, os.R_OK):
            print(f"No read permission for {input_file}")
            return
        if os.path.getsize(input_file) == 0:
            print(f"Input file {input_file} is empty")
            with open(output_file, 'wb') as f:
                f.write(bytes([0]))
            return

        filetype = detect_filetype(input_file)
        success = compressor.compress(input_file, output_file, filetype, mode)
        if success:
            orig_size = os.path.getsize(input_file)
            comp_size = os.path.getsize(output_file)
            ratio = (comp_size / orig_size) * 100 if orig_size > 0 else 0
            print(f"Compression successful: {output_file}, Size: {comp_size} bytes")
            print(f"Original: {orig_size} bytes, Compressed: {comp_size} bytes, Ratio: {ratio:.2f}%")
        else:
            print("Compression failed")

    elif choice == '2':
        input_file = input("Enter input file path: ").strip()
        output_file = input("Enter output file path: ").strip()

        if not os.path.exists(input_file):
            print(f"Input file {input_file} not found")
            return
        if not os.access(input_file, os.R_OK):
            print(f"No read permission for {input_file}")
            return
        if os.path.getsize(input_file) == 0:
            print(f"Input file {input_file} is empty")
            with open(output_file, 'wb') as f:
                f.write(b'')
            return

        success = compressor.decompress(input_file, output_file)
        if success:
            comp_size = os.path.getsize(input_file)
            decomp_size = os.path.getsize(output_file)
            print(f"Decompression successful: {output_file}")
            print(f"Compressed: {comp_size} bytes, Decompressed: {decomp_size} bytes")
        else:
            print("Decompression failed")

if __name__ == "__main__":
    main()
