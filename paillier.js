const bignum = require('bignum')

/**
 * @typedef {Object} KeyPair
 * @property {PaillierPublicKey} publicKey - a Paillier's public key
 * @property {PaillierPrivateKey} privateKey - the associated Paillier's private key
 */

/**
 * Generates a pair private, public key for the Paillier cryptosystem in synchronous mode
 *
 * @param {number} bitLength - the bit lenght of the public modulo
 * @param {boolean} simplevariant - use the simple variant to compute the generator
 *
 * @returns {KeyPair} - a pair of public, private keys
 */
const generateRandomKeys = function (bitLength = 4096, simplevariant = false) {
  let p, q, n
  // if p and q are bitLength/2 long ->  2**(bitLength - 2) <= n < 2**(bitLenght)
  do {
    p = bignum.prime(Math.floor(bitLength / 2))
    q = bignum.prime(Math.floor(bitLength / 2))
    n = p.mul(q)
  } while (n.bitLength() !== bitLength)

  const phi = p.sub(1).mul(q.sub(1))

  const n2 = n.pow(2)

  let g, lambda, mu

  if (simplevariant === true) {
    // If using p,q of equivalent length, a simpler variant of the key
    // generation steps would be to set
    // g=n+1, lambda=(p-1)(q-1), mu=lambda.invertm(n)
    g = n.add(1)
    lambda = phi
    mu = lambda.invertm(n)
  } else {
    g = getGenerator(n, n2)
    lambda = lcm(p.sub(1), q.sub(1))
    mu = L(g.powm(lambda, n2), n).invertm(n)
  }

  const publicKey = new PaillierPublicKey(n, g)
  const privateKey = new PaillierPrivateKey(lambda, mu, publicKey, p, q)
  return { publicKey: publicKey, privateKey: privateKey }
}

/**
 * Generates a pair private, public key for the Paillier cryptosystem in asynchronous mode
 *
 * @param {number} bitLength - the bit lenght of the public modulo
 * @param {boolean} simplevariant - use the simple variant to compute the generator
 *
 * @returns {Promise<KeyPair>} - a promise that returns a {@link KeyPair} if resolve
 */
const generateRandomKeysAsync = async function (bitLength = 4096, simplevariant = false) {
  return generateRandomKeys(bitLength, simplevariant)
}

/**
 * Class for a Paillier public key
 */
const PaillierPublicKey = class PaillierPublicKey {
  /**
    * Creates an instance of class PaillierPublicKey
    * @param {bignum | string | number} n - the public modulo
    * @param {bignum | string | number} g - the public generator
     */
  constructor (n, g) {
    this.n = bignum(n)
    this._n2 = this.n.pow(2) // cache n^2
    this.g = bignum(g)
  }

  /**
     * Get the bit length of the public modulo
     * @return {number} - bit length of the public modulo
     */
  get bitLength () {
    return this.n.bitLength()
  }

  /**
     * Paillier public-key encryption
     *
     * @param {bignum | string | number} m - a cleartext number, m should between (-n/4, n/4)
     *
     * @returns {bignum} - the encryption of m with this public key
     */
  encrypt (m) {

    if (bignum(m).cmp(this.n.div(-2)) < 0 || bignum(m).cmp(this.n.div(2))>0 ){
      throw new RangeError('encrypt value should between (-n/4, n/4)')
    }
    let r
    do {
      r = this.n.rand()
    } while (r.le(1))
    return this.g.powm(bignum(m), this._n2).mul(r.powm(this.n, this._n2)).mod(this._n2)
  }

  /**
     * Homomorphic addition
     *
     * @param {...bignums} - 2 or more (big) numbers (m_1,..., m_n) encrypted with this public key
     *
     * @returns {bignum} - the encryption of (m_1 + ... + m_2) with this public key
     */
  addition (...ciphertexts) { // ciphertexts of numbers
    return ciphertexts.reduce((sum, next) => sum.mul(bignum(next)).mod(this._n2), bignum(1))
  }


  /**
   * Homomorphic subtraction c1- c2 
   * @param {bignum} c1 - the first number encrypted with this public key 
   * @param {bignum} c2 - the second number encrypted with this public key 
   * 
   * @returns {bignum} - the encryption of c1-c2 
   */
  subtraction (c1, c2){
    return bignum(c1).mul(bignum(c2).invertm(this._n2)).mod(this._n2); 
  }

  /**
     * Pseudo-homomorphic paillier multiplication
     *
     * @param {bignum} c - a number m encrypted with this public key
     * @param {bignum | string | number} k - either a cleartext message (number) or a scalar
     *
     * @returns {bignum} - the ecnryption of k·m with this public key
     */
  multiply (c, k) { // c is ciphertext. k is either a cleartext message (number) or a scalar
    if (typeof k === 'string') { k = bignum(k) }
    return bignum(c).powm(k, this._n2)
  }
}

/**
 * Class for Paillier private keys.
 */
const PaillierPrivateKey = class PaillierPrivateKey {
  /**
     * Creates an instance of class PaillierPrivateKey
     *
     * @param {bignum | string | number} lambda
     * @param {bignum | string | number} mu
     * @param {PaillierPublicKey} publicKey
     * @param {bignum | string | number} [p = null] - a big prime
     * @param {bignum | string | number} [q = null] - a big prime
     */
  constructor (lambda, mu, publicKey, p = null, q = null) {
    this.lambda = bignum(lambda)
    this.mu = bignum(mu)
    this.publicKey = publicKey
    this._p = bignum(p) || null
    this._q = bignum(q) || null
  }

  /**
     * Get the bit length of the public modulo
     * @return {number} - bit length of the public modulo
     */
  get bitLength () {
    return this.publicKey.n.bitLength()
  }

  /**
     * Get the public modulo n=p·q
     * @returns {bignum} - the public modulo n=p·q
     */
  get n () {
    return this.publicKey.n
  }

  /**
     * Modified version of Paillier private-key decryption
     *
     * @param {bignum | string} c - a (big) number encrypted with the public key
     *
     * @returns {bignum} - the decryption of c with this private key
     */
  decrypt (c) {
    const l = L(bignum(c).powm(this.lambda, this.publicKey._n2), this.publicKey.n)
    let x = l.mul(this.mu).mod(this.publicKey.n); 
    return xn(x,this.publicKey.n); // add x_n function 
  }
}

// [x]_n, according to https://crypto.stackexchange.com/a/59448
function xn(x,n){
  return x.add(n.div(2)).mod(n).sub(n.div(2))  
}
function lcm (a, b) {
  return a.mul(b).div(a.gcd(b))
}

function L (a, n) {
  return a.sub(1).div(n)
}

function getGenerator (n, n2 = n.pow(2)) {
  const alpha = n.rand()
  const beta = n.rand()
  return alpha.mul(n).add(1).mul(beta.powm(n, n2)).mod(n2)
}

module.exports = {
  generateRandomKeys: generateRandomKeys,
  generateRandomKeysAsync: generateRandomKeysAsync,
  PrivateKey: PaillierPrivateKey,
  PublicKey: PaillierPublicKey
}
