#----------------------------Packages-----------------------------------------
require(MASS)
require(Matrix)
#----------------------Envelope functions-------------------------------
u.env_modified <- function(X, Y, alpha = 0.01, maxiter = 100, ftol = 1e-3) {
  
  X <- as.matrix(X)
  a <- dim(Y)
  n <- a[1]
  r <- a[2]
  p <- ncol(X)
  
  loglik.seq <- unlist(lapply(0:r, function(x) env_modified(X, Y, x, asy = F, maxiter = maxiter, ftol = ftol)$loglik))
  npara.seq <- r + r * (r + 1) / 2 + p * (0:r)
  
  aic.seq <- -2 * loglik.seq + 2 * npara.seq
  bic.seq <- -2 * loglik.seq + log(n) * npara.seq
  
  u.aic <- which.min(aic.seq) - 1
  u.bic <- which.min(bic.seq) - 1
  
  lrt.test <- pchisq(2 * (loglik.seq[r + 1] - loglik.seq[1:r]), npara.seq[r + 1] - npara.seq[1:r], lower.tail = F)
  
  if (any(lrt.test > alpha)) {
    u.lrt <- which(lrt.test > alpha)[1] - 1
  } else {
    u.lrt <- r
  }
  
  return(list(u.aic = u.aic, u.bic = u.bic, u.lrt = u.lrt, loglik.seq = loglik.seq, aic.seq = aic.seq, bic.seq = bic.seq))
}

GE <- function (A){
  a <- dim(A)
  n <- a[1]
  p <- a[2]
  idx <- rep(0, p)
  res.idx <- 1:n
  i <- 1
  while (i <= p) {
    tmp <- max(abs(A[res.idx, i]))
    Stmp <- setdiff(which(abs(A[, i]) == tmp), idx)
    idx[i] <- Stmp[1]
    res.idx <- setdiff(res.idx, idx[i])
    for (j in 1:(n - i)) {
      A[res.idx[j], ] <- A[res.idx[j], ] - A[res.idx[j], 
                                             i]/A[idx[i], i] * A[idx[i], ]
    }
    i <- i + 1
  }
  c(idx, res.idx)
}

envMU_modified <- function(M, U, u, maxiter = 100, ftol = 1e-3) {
  # print(maxiter)
  # print(ftol)
  dimM <- dim(M)
  dimU <- dim(U)
  r <- dimM[1]
  
  if (dimM[1] != dimM[2] & dimU[1] != dimU[2]) stop("M and U should be square matrices.")
  if (dimM[1] != dimU[1]) stop("M and U should have the same dimension.")
  # if (rankMatrix(M) < r) stop("M should be positive definite.")
  if (rankMatrix(M) < r) M=M+0.01*diag(nrow(M))
  if (u > r & u < 0) stop("u should be between 0 and r.")
  
  
  if (u == 0) {
    
    Gammahat <- NULL
    Gamma0hat <- diag(r)
    MU <- M + U
    tmp.MU <- eigen(MU)
    objfun <- sum(log(tmp.MU$values))
    
  } else if (u == r) {
    
    Gammahat <- diag(r)
    Gamma0hat <- NULL
    tmp.M <- eigen(M)
    objfun <- sum(log(tmp.M$values))
    
  } else if (u == r - 1) {
    
    # maxiter = 100
    # ftol = 1e-3
    
    MU <- M + U
    tmp.MU <- eigen(MU)
    invMU <- sweep(tmp.MU$vectors, MARGIN = 2, 1 / tmp.MU$values, '*') %*% t(tmp.MU$vectors)
    invMU2 <- sweep(tmp.MU$vectors, MARGIN = 2, 1 / sqrt(tmp.MU$values), '*') %*% t(tmp.MU$vectors)
    
    midmatrix <- U
    startv <- function(a) t(a) %*% midmatrix %*% a
    tmp2.MU <- apply(tmp.MU$vectors, 2, startv)
    tmp3.MU <- sort(tmp2.MU, decreasing = TRUE, index.return = TRUE)
    init <- as.matrix(tmp.MU$vectors[, tmp3.MU$ix[1:u]]) 
    
    #	  if (qr(MU)$rank == r) {
    eig1 <- eigen(t(init) %*% M %*% init)
    eig2 <- eigen(t(init) %*% invMU %*% init)
    obj1 <- sum(log(eig1$values)) + sum(log(eig2$values))
    
    midmatrix <- invMU2 %*% tcrossprod(U, invMU2) 
    tmp2.MU <- apply(tmp.MU$vectors, 2, startv)
    tmp3.MU <- sort(tmp2.MU, decreasing = TRUE, index.return = TRUE)
    init.MU <- as.matrix(tmp.MU$vectors[, tmp3.MU$ix[1:u]])
    e1 <- eigen(t(init.MU) %*% M %*% init.MU)
    e2 <- eigen(t(init.MU) %*% invMU %*% init.MU)
    obj2 <- sum(log(e1$values)) + sum(log(e2$values))		
    if (obj2 < obj1) {
      init <- init.MU
      obj1 <- obj2
    }
    
    #	    if (qr(M)$rank == r) {
    tmp.M <- eigen(M)
    midmatrix <- U
    tmp2.M <- apply(tmp.M$vectors, 2, startv)
    tmp3.M <- sort(tmp2.M, decreasing = TRUE, index.return = TRUE)	
    init.M <- as.matrix(tmp.M$vectors[, tmp3.M$ix[1:u]])
    e1 <- eigen(t(init.M) %*% M %*% init.M)
    e2 <- eigen(t(init.M) %*% invMU %*% init.M)
    obj3 <- sum(log(e1$values)) + sum(log(e2$values))			
    if (obj3 < obj1) {
      init <- init.M
      obj1 <- obj3
    }
    
    invM2 <- sweep(tmp.M$vectors, MARGIN = 2, 1 / sqrt(tmp.M$values), '*') %*% t(tmp.M$vectors)
    midmatrix <- invM2 %*% tcrossprod(U, invM2) 
    tmp2.M <- apply(tmp.M$vectors, 2, startv)
    tmp3.M <- sort(tmp2.M, decreasing = TRUE, index.return = TRUE)
    init.M <- as.matrix(tmp.M$vectors[, tmp3.M$ix[1:u]])				
    
    e1 <- eigen(t(init.M) %*% M %*% init.M)
    e2 <- eigen(t(init.M) %*% invMU %*% init.M)			
    obj4 <- sum(log(e1$values)) + sum(log(e2$values))			
    if (obj4 < obj1) {
      init <- init.M
      obj1 <- obj4
    }
    #	    }
    #	  }
    
    GEidx <- GE(init)
    Ginit <- init %*% solve(init[GEidx[1:u], ])		
    
    j <- GEidx[r]
    
    g <- as.matrix(Ginit[j, ])
    t2 <- crossprod(Ginit[-j, ], as.matrix(M[-j, j])) / M[j, j]
    t3 <- crossprod(Ginit[-j, ], as.matrix(invMU[-j, j])) / invMU[j, j]
    
    GUGt2 <- g + t2
    GUG <- crossprod(Ginit, (M %*% Ginit)) - tcrossprod(GUGt2, GUGt2) * M[j, j]
    
    GVGt2 <- g + t3
    GVG <- crossprod(Ginit, (invMU %*% Ginit)) - tcrossprod(GVGt2, GVGt2) * invMU[j, j] 
    
    invC1 <- chol2inv(chol(GUG))
    invC2 <- chol2inv(chol(GVG))
    
    fobj <- function(x) {
      tmp2 <- x + t2
      tmp3 <- x + t3
      T2 <- invC1 %*% tmp2	
      T3 <- invC2 %*% tmp3
      -2 * log(1 + sum(x^2)) + log(1 + M[j, j] * crossprod(tmp2, T2)) + log(1 + invMU[j, j] * crossprod(tmp3, T3))
    }
    
    gobj <- function(x) {
      tmp2 <- x + t2
      tmp3 <- x + t3
      T2 <- invC1 %*% tmp2	
      T3 <- invC2 %*% tmp3
      -4 	* x %*% solve(1 + sum(x^2)) + 2 * T2 / as.numeric(1 / M[j, j] + crossprod(tmp2, T2)) + 2 * T3 / as.numeric(1 / invMU[j, j] + crossprod(tmp3, T3))	
    }
    
    i <- 1
    while (i < maxiter) {
      
      res <- optim(Ginit[j,], fobj, gobj, method = "BFGS")
      Ginit[j, ] <- res$par
      
      a <- qr(Ginit)
      Gammahat <- qr.Q(a)
      e1 <- eigen(t(Gammahat) %*% M %*% Gammahat)
      e2 <- eigen(t(Gammahat) %*% invMU %*% Gammahat)				
      obj5 <- sum(log(e1$values)) + sum(log(e2$values))	
      if (abs(obj1 - obj5) < ftol * abs(obj1)) {
        break
      } else {
        obj1 <- obj5
        i <- i + 1
      }
    }
    
    Gamma0hat <- qr.Q(a, complete = TRUE)[, (u+1):r, drop = FALSE]
    objfun <- obj5 + sum(log(tmp.MU$values))
    
  } else {
    
    # maxiter = 100
    # ftol = 1e-3
    
    
    MU <- M + U
    tmp.MU <- eigen(MU)
    invMU <- sweep(tmp.MU$vectors, MARGIN = 2, 1 / tmp.MU$values, '*') %*% t(tmp.MU$vectors)
    invMU2 <- sweep(tmp.MU$vectors, MARGIN = 2, 1 / sqrt(tmp.MU$values), '*') %*% t(tmp.MU$vectors)
    
    midmatrix <- U
    startv <- function(a) t(a) %*% midmatrix %*% a
    tmp2.MU <- apply(tmp.MU$vectors, 2, startv)
    tmp3.MU <- sort(tmp2.MU, decreasing = TRUE, index.return = TRUE)
    init <- as.matrix(tmp.MU$vectors[, tmp3.MU$ix[1:u]]) 
    
    #		if (qr(MU)$rank == r) {
    eig1 <- eigen(t(init) %*% M %*% init)
    eig2 <- eigen(t(init) %*% invMU %*% init)
    obj1 <- sum(log(eig1$values)) + sum(log(eig2$values))
    
    midmatrix <- invMU2 %*% tcrossprod(U, invMU2) 
    tmp2.MU <- apply(tmp.MU$vectors, 2, startv)
    tmp3.MU <- sort(tmp2.MU, decreasing = TRUE, index.return = TRUE)
    init.MU <- as.matrix(tmp.MU$vectors[, tmp3.MU$ix[1:u]])
    e1 <- eigen(t(init.MU) %*% M %*% init.MU)
    e2 <- eigen(t(init.MU) %*% invMU %*% init.MU)
    obj2 <- sum(log(e1$values)) + sum(log(e2$values))		
    if (obj2 < obj1) {
      init <- init.MU
      obj1 <- obj2
    }
    
    #			if (qr(M)$rank == r) {
    tmp.M <- eigen(M)
    midmatrix <- U
    tmp2.M <- apply(tmp.M$vectors, 2, startv)
    tmp3.M <- sort(tmp2.M, decreasing = TRUE, index.return = TRUE)	
    init.M <- as.matrix(tmp.M$vectors[, tmp3.M$ix[1:u]])
    e1 <- eigen(t(init.M) %*% M %*% init.M)
    e2 <- eigen(t(init.M) %*% invMU %*% init.M)
    obj3 <- sum(log(e1$values)) + sum(log(e2$values))			
    if (obj3 < obj1) {
      init <- init.M
      obj1 <- obj3
    }
    
    invM2 <- sweep(tmp.M$vectors, MARGIN = 2, 1 / sqrt(tmp.M$values), '*') %*% t(tmp.M$vectors)
    midmatrix <- invM2 %*% tcrossprod(U, invM2) 
    tmp2.M <- apply(tmp.M$vectors, 2, startv)
    tmp3.M <- sort(tmp2.M, decreasing = TRUE, index.return = TRUE)
    init.M <- as.matrix(tmp.M$vectors[, tmp3.M$ix[1:u]])				
    
    e1 <- eigen(t(init.M) %*% M %*% init.M)
    e2 <- eigen(t(init.M) %*% invMU %*% init.M)			
    obj4 <- sum(log(e1$values)) + sum(log(e2$values))			
    if (obj4 < obj1) {
      init <- init.M
      obj1 <- obj4
    }
    #			}
    #		}
    
    GEidx <- GE(init)
    Ginit <- init %*% solve(init[GEidx[1:u], ])
    
    
    GUG <- crossprod(Ginit, (M %*% Ginit))	
    GVG <- crossprod(Ginit, (invMU %*% Ginit))		
    
    
    t4 <- crossprod(Ginit[GEidx[(u+1):r],], Ginit[GEidx[(u+1):r], ]) + diag(u)
    i <- 1
    while (i < maxiter) {
      
      for (j in GEidx[(u+1):r]) {
        g <- as.matrix(Ginit[j, ])
        t2 <- crossprod(Ginit[-j, ], as.matrix(M[-j, j])) / M[j, j]
        t3 <- crossprod(Ginit[-j, ], as.matrix(invMU[-j, j])) / invMU[j, j]
        
        GUGt2 <- g + t2
        GUG <- GUG - tcrossprod(GUGt2, GUGt2) * M[j, j]
        
        GVGt2 <- g + t3
        GVG <- GVG - tcrossprod(GVGt2, GVGt2) * invMU[j, j] 
        
        t4 <- t4 - tcrossprod(g, g)
        invC1 <- chol2inv(chol(GUG))
        invC2 <- chol2inv(chol(GVG))
        invt4 <- chol2inv(chol(t4))				
        
        fobj <- function(x) {
          tmp2 <- x + t2
          tmp3 <- x + t3
          T1 <- invt4 %*% x
          T2 <- invC1 %*% tmp2	
          T3 <- invC2 %*% tmp3
          -2 * log(1 + x %*% T1) + log(1 + M[j, j] * crossprod(tmp2, T2)) + log(1 + invMU[j, j] * crossprod(tmp3, T3))
        }
        
        gobj <- function(x) {
          tmp2 <- x + t2
          tmp3 <- x + t3
          T1 <- invt4 %*% x
          T2 <- invC1 %*% tmp2	
          T3 <- invC2 %*% tmp3
          -4 	* T1 / as.numeric(1 + x %*% T1) + 2 * T2 / as.numeric(1 / M[j, j] + crossprod(tmp2, T2)) + 2 * T3 / as.numeric(1 / invMU[j, j] + crossprod(tmp3, T3))	
        }
        
        res <- optim(Ginit[j,], fobj, gobj, method = "BFGS")
        Ginit[j, ] <- res$par
        g <- as.matrix(Ginit[j, ])
        t4 <- t4 + tcrossprod(g, g)
        GUGt2 <- g + t2
        GUG <- GUG + tcrossprod(GUGt2, GUGt2) * M[j, j]
        
        GVGt2 <- g + t3
        GVG <- GVG + tcrossprod(GVGt2, GVGt2) * invMU[j, j] 
        
        
      }
      a <- qr(Ginit)
      Gammahat <- qr.Q(a)
      e1 <- eigen(t(Gammahat) %*% M %*% Gammahat)
      e2 <- eigen(t(Gammahat) %*% invMU %*% Gammahat)				
      obj5 <- sum(log(e1$values)) + sum(log(e2$values))	
      if (abs(obj1 - obj5) < ftol * abs(obj1)) {
        break
      } else {
        obj1 <- obj5
        i <- i + 1
      }
    }
    
    Gamma0hat <- qr.Q(a, complete = TRUE)[, (u+1):r]
    objfun <- obj5 + sum(log(tmp.MU$values))
    
  }
  return(list(Gammahat = Gammahat, Gamma0hat = Gamma0hat, objfun = objfun))
}

env_modified <- function(X, Y, u, asy = TRUE, maxiter = 100, ftol = 1e-3) {
  # print(u)
  X <- as.matrix(X)
  Y <- as.matrix(Y)
  a <- dim(Y)
  n <- a[1]
  r <- a[2]
  p <- ncol(X)
  
  if (a[1] != nrow(X)) stop("X and Y should have the same number of observations.")
  if (u > r || u < 0) stop("u must be an integer between 0 and r.")
  if(sum(duplicated(cbind(X, Y), MARGIN = 2)) > 0) stop("Some responses also appear in the predictors, or there maybe duplicated columns in X or Y.")
  
  sigY <- cov(Y) * (n - 1) / n
  sigYX <- cov(Y, X) * (n - 1) / n
  sigX <- cov(X) * (n - 1) / n
  if(rankMatrix(sigX)!=nrow(sigX)){
    sigX=0.01*diag(nrow(sigX))+sigX
  }
  invsigX <- chol2inv(chol(sigX))
  betaOLS <- sigYX %*% invsigX
  
  U <- tcrossprod(betaOLS, sigYX) 
  M <- sigY - U
  
  tmp <- envMU_modified(M, U, u, maxiter = maxiter, ftol = ftol)
  Gammahat <- tmp$Gammahat
  Gamma0hat <- tmp$Gamma0hat
  objfun <- tmp$objfun
  covMatrix <- NULL
  asySE <- NULL
  ratio <- NULL 
  asyFm <- NULL
  if (u == 0) {
    
    etahat <- NULL
    Omegahat <- NULL
    Omega0hat <- sigY
    alphahat <- colMeans(Y)
    betahat <- matrix(0, r, p)
    Sigmahat <- sigY
    loglik <- - n * r / 2 * (log(2 * pi) + 1) - n / 2 * objfun
    if (asy == T) {
      ratio <- matrix(10^10, r, p) # the ratio of sd(ols)/sd(env) should be infinity, we set as a large number here
      # if (asy == T) ratio <- matrix(1, r, p)
      asySE <- matrix(0, r, p)
      covMatrix <- kronecker(invsigX, M)
      asyFm <- matrix(sqrt(diag(covMatrix)), nrow = r)
    }
  } else if (u == r) {
    
    etahat <- betaOLS
    Omegahat <- diag(r)
    Omega0hat <- NULL
    alphahat <- colMeans(Y) - betaOLS %*% colMeans(X)
    betahat <- betaOLS
    Sigmahat <- M
    loglik <- - n * r / 2 * (log(2 * pi) + 1) - n / 2 * objfun
    if (asy == T) {
      covMatrix <- kronecker(invsigX, M)
      asySE <- matrix(sqrt(diag(covMatrix)), nrow = r)
      ratio <- matrix(1, r, p)
    }
    
  } else {
    
    etahat <- crossprod(Gammahat, betaOLS)
    betahat <- Gammahat %*% etahat
    alphahat <- colMeans(Y) - betahat %*% colMeans(X)
    Omegahat <- crossprod(Gammahat, M) %*% Gammahat
    Omega0hat <- crossprod(Gamma0hat, sigY) %*% Gamma0hat
    Sigma1 <- Gammahat %*% tcrossprod(Omegahat, Gammahat)
    Sigmahat <- Sigma1 + Gamma0hat %*% tcrossprod(Omega0hat, Gamma0hat)
    loglik <- - n * r / 2 * (log(2 * pi) + 1) - n / 2 * objfun
    if (asy == T) {
      covMatrix <- kronecker(invsigX, M)
      asyFm <- matrix(sqrt(diag(covMatrix)), nrow = r)
      invOmega0hat <- chol2inv(chol(Omega0hat))
      invOmegahat <- chol2inv(chol(Omegahat))
      temp <- kronecker(etahat %*% tcrossprod(sigX, etahat), invOmega0hat) + kronecker(invOmegahat, Omega0hat) + kronecker(Omegahat, invOmega0hat) - 2 * kronecker(diag(u), diag(r - u))
      temp2 <- kronecker(t(etahat), Gamma0hat)
      covMatrix <- kronecker(invsigX, Sigma1) + temp2 %*% chol2inv(chol(temp)) %*% t(temp2)
      asySE <- matrix(sqrt(diag(covMatrix)), nrow = r)
      ratio <- asyFm / asySE
    }    
  }
  
  return(list(Gamma = Gammahat, Gamma0 = Gamma0hat, alpha = alphahat, beta = betahat, Sigma = Sigmahat, eta = etahat, Omega = Omegahat, Omega0 = Omega0hat, loglik = loglik, n = n, covMatrix = covMatrix, asySE_env = asySE, ratio = ratio, asySE_ols = asyFm))
}

#---------------------------------Functions-----------------------------------
#Projection matrix
P <- function(A){
  A %*% ginv(t(A)%*%A) %*% t(A)
}
Q <- function(A){
  a <- nrow(A)
  diag(a) - P(A)
}

#Input a vector, output a permutation matrix related to the location of NAs
Pmt <- function(x){
  l <- length(x)
  if(anyNA(x) == 0)
    return(diag(l))
  a <- is.na(x)
  index <- which(a) #index of missing data
  A <- matrix(rep(0, l^2), nrow = l)
  pmt_vec <- c(index, setdiff(1:l, index))
  for (i in 1:l) {
    A[i, which(pmt_vec == i)] <- 1
  }
  return(A)
}

#Input a matrix, output the L1-norm of it.
l1_norm <- function(A){
  return(sum(abs(A)))
}

#Function for calculating A_1, A_2, A_3, A_4
moment_matrix <- function(x, y, mu, Sigma_x, Sigma_y, Beta){
  B11 <- solve(Sigma_x) + Beta %*% solve(Sigma_y) %*% t(Beta)
  B12 <- -Beta %*% solve(Sigma_y)
  B21 <- t(B12)
  B22 <- solve(Sigma_y)
  Sigma <- solve(rbind(cbind(B11, B12), cbind(B21, B22)))
  mu_z <- c(mu, t(Beta) %*% mu)
  l_na_x <- sum(is.na(x))
  l_na_y <- sum(is.na(y))
  z <- c(x, y)
  if(anyNA(z) == 0){
    A_1 <- y %*% t(y)
    A_2 <- y %*% t(x)
    A_3 <- x %*% t(x)
    A_4 <- matrix(x)
    return(list(A_1, A_2, A_3, A_4))
  }
  
  A <- Pmt(z)
  A_x <- Pmt(x)
  A_y <- Pmt(y)
  l_na_z <- l_na_x + l_na_y
  mu_z_tilde <- t(A) %*% mu_z
  mu_z_miss <- mu_z_tilde[1:l_na_z]
  mu_z_obs <- mu_z_tilde[-1:-l_na_z]
  z_obs <- na.omit(z)
  y_obs <- na.omit(y)
  x_obs <- na.omit(x)
  Sigma_tilde <- t(A) %*% Sigma %*% A
  Sigma_11 <- Sigma_tilde[1:l_na_z, 1:l_na_z]
  if(l_na_z == 1)
    Sigma_12 <- matrix(Sigma_tilde[1:l_na_z, -1:-l_na_z], nrow = 1)
  else
    Sigma_12 <- Sigma_tilde[1:l_na_z, -1:-l_na_z]
  Sigma_21 <- t(Sigma_12)
  Sigma_22 <- Sigma_tilde[-1:-l_na_z, -1:-l_na_z]
  Sigma_11.2 <- Sigma_11 - Sigma_12 %*% solve(Sigma_22) %*% Sigma_21
  E_z_miss <- mu_z_miss + Sigma_12 %*% solve(Sigma_22) %*% (z_obs - mu_z_obs)
  if(l_na_x == 0){
    A_3 <- x %*% t(x)
    A_4 <- matrix(x)
    E_y_miss <- E_z_miss
    E_y_tilde <- c(E_y_miss, y_obs)
    E_y <- A_y %*% E_y_tilde
    A_2 <- E_y %*% t(x)
    N11 <- Sigma_11.2 + E_y_miss %*% t(E_y_miss)
    N12 <- E_y_miss %*% t(y_obs)
    N21 <- t(N12)
    N22 <- y_obs %*% t(y_obs)
    A_1 <- A_y %*% rbind(cbind(N11, N12), cbind(N21, N22)) %*% t(A_y)
    return(list(A_1, A_2, A_3, A_4))
  }
  if(l_na_y == 0){
    A_1 <- y %*% t(y)
    E_x_miss <- E_z_miss
    A_4 <- A_x %*% c(E_x_miss, x_obs)
    A_2 <- y %*% t(A_4)
    M11 <- Sigma_11.2 + E_x_miss %*% t(E_x_miss)
    M12 <- E_x_miss %*% t(x_obs)
    M21 <- t(M12)
    M22 <- x_obs %*% t(x_obs)
    M <- rbind(cbind(M11, M12), cbind(M21, M22))
    A_3 <- A_x %*% M %*% t(A_x)
    return(list(A_1, A_2, A_3, A_4))
  }
  E_x_miss <- E_z_miss[1:l_na_x]
  E_y_miss <- E_z_miss[-1:-l_na_x]
  A_4 <- A_x %*% c(E_x_miss, x_obs)
  E_y_tilde <- c(E_y_miss, y_obs)
  Sigma_x_miss <- Sigma_11.2[1:l_na_x, 1:l_na_x]
  M11 <- Sigma_x_miss + E_x_miss %*% t(E_x_miss)
  M12 <- E_x_miss %*% t(x_obs)
  M21 <- t(M12)
  M22 <- x_obs %*% t(x_obs)
  M <- rbind(cbind(M11, M12), cbind(M21, M22))
  A_3 <- A_x %*% M %*% t(A_x)
  Sigma_y_miss <- Sigma_11.2[-1:-l_na_x, -1:-l_na_x]
  N11 <- Sigma_y_miss + E_y_miss %*% t(E_y_miss)
  N12 <- E_y_miss %*% t(y_obs)
  N21 <- t(N12)
  N22 <- y_obs %*% t(y_obs)
  N <- rbind(cbind(N11, N12), cbind(N21, N22))
  A_1 <- A_y %*% N %*% t(A_y)
  Sigma_xy_miss <- Sigma_11.2[-1:-l_na_x, 1:l_na_x]
  O11 <- Sigma_xy_miss + E_y_miss %*% t(E_x_miss)
  O12 <- E_y_miss %*% t(x_obs)
  O21 <- y_obs %*% t(E_x_miss)
  O22 <- y_obs %*% t(x_obs)
  O <- rbind(cbind(O11, O12), cbind(O21, O22))
  A_2 <- A_y %*% O %*% t(A_x)
  return(list(A_1, A_2, A_3, A_4))
}

sum_A1234 <- function(X, Y, mu, Sigma_x, Sigma_y, beta){
  n <- nrow(X)
  A <- 0
  for(i in 1:n)
    A <- mapply("+", A, moment_matrix(X[i, ], Y[i, ], mu, Sigma_x, Sigma_y, beta))
  return(A)
}

#Use 1D-algorithm. Input a list of matrix A = {A1, A2, A3, A4}, and envelope dimension u
gamma_1D <- function(A, u){
  q <- nrow(A[[1]])
  G_k = rep(0, q)
  for (i in 0:(u-1)) {
    G_0k = qr.Q(qr(G_k),complete=TRUE)[, (i+1):q]
    D_k <- function(w){
      M = t(G_0k) %*% (A[[1]] - A[[2]] %*% solve(A[[3]]) %*% t(A[[2]])) %*% G_0k
      M <- (M + t(M))/2
      U = t(G_0k) %*% solve(A[[1]]) %*% G_0k
      U <- (U + t(U))/2
      return(log(t(w) %*% M %*% w) + log(t(w) %*% U %*% w) - 2*log(t(w) %*% w))
      #return(exp(t(w) %*% M %*% w * t(w) %*% U %*% w /(t(w) %*% w)^2))
    }
    eig_M <- eigen(t(G_0k) %*% (A[[1]]) %*% G_0k)
    opt <- optim(eig_M$vectors[, 1], D_k, method = "CG")
    w_k <- opt$par
    g_k <- (G_0k %*% w_k)/sqrt(sum(w_k^2))
    if(i == 0)
      G_k = g_k
    else
      G_k = cbind(G_k, g_k)
  }
  return(G_k)
}


#Update of parameters using EM-algorithm
update_par <- function(X, Y, mu, Sigma_x, Sigma_y, beta, u){
  n = nrow(X)
  A <- sum_A1234(X, Y, mu, Sigma_x, Sigma_y, beta)
  A[[1]] <- (A[[1]] + t(A[[1]]))/2 + 0.05 * diag(nrow(A[[1]]))
  A[[3]] <- (A[[3]] + t(A[[3]]))/2 + 0.05 * diag(nrow(A[[3]]))
  mu_update <- A[[4]]/n
  Sigma_x_update <- (A[[3]] - 2*A[[4]] %*% t(mu_update))/n + mu_update %*% t(mu_update)
  Sigma_x_update <- (Sigma_x_update + t(Sigma_x_update))/2
  gamma_env <- gamma_1D(A, u)
  #gamma_env <- GAMMA
  Sigma1 <- P(gamma_env) %*% (A[[1]] - A[[2]] %*% solve(A[[3]]) %*% t(A[[2]])) %*% P(gamma_env)/n
  Sigma2 <- Q(gamma_env) %*% A[[1]] %*% Q(gamma_env)/n
  Sigma_y_update <- Sigma1 + Sigma2
  Sigma_y_update <- (Sigma_y_update + t(Sigma_y_update))/2
  beta_update <- solve(A[[3]]) %*% t(A[[2]]) %*% P(Sigma1)
  bic = dim(X)[1] * log(det(P(gamma_env) %*% (A[[1]] - A[[2]] %*% solve(A[[3]]) %*% t(A[[2]])) %*% P(gamma_env) + Q(gamma_env) %*% (A[[1]]) %*% Q(gamma_env))) + dim(X)[2]*u * log(dim(X)[1])
  DET1 <- det((A[[1]] - A[[2]] %*% solve(A[[3]]) %*% t(A[[2]])))
  EIGENVALUE <- eigen((A[[1]] - A[[2]] %*% solve(A[[3]]) %*% t(A[[2]])))$values
  DET2 <-  det(A[[1]])
  return(list(mu_update, Sigma_x_update, Sigma_y_update, beta_update, gamma_env, bic, DET1, EIGENVALUE, DET2))
}
#--------------------------Generate data（0.1 missing rate）---------------------------
set.seed(1234)
num = 500
env_dim <- 3
p = 5
q = 20
GAMMA <- matrix(runif(env_dim * q), nrow = q)
beta0 <- matrix(runif(p * q, -10, 10), nrow = p)
beta <- beta0 %*% P(GAMMA)
Omega <- 0.1 * diag(nrow(GAMMA))
Omega0 <- 10 * diag(nrow(GAMMA))
Sigma_y <- P(GAMMA) %*% Omega %*% P(GAMMA) + Q(GAMMA) %*% Omega0 %*% Q(GAMMA)
A <- matrix(runif(p ^ 2, -10, 10), nrow = p)
mu_x <- runif(p, -10, 10)
Sigma_x <- A %*% t(A)

MSE_env_em <- NULL
MSE_comp_ols <- NULL
MSE_comp_env <- NULL
MSE_lb <- NULL
for(j in 1:3){
  tryCatch({
    
    X <- mvrnorm(num, mu_x, Sigma_x)
    Y <- X %*% beta + mvrnorm(num, rep(0, q), Sigma_y)
    MSE_lb <- c(sum(t(env_modified(X, Y, 3)$beta) - beta)^2/(p * q), MSE_lb)
    #insert code here
    X_scale <- apply(X, 2, FUN = scale)
    Y_scale <- apply(Y, 2, FUN = scale)
    #Generate missing data for X
    for (i in 1:dim(X_scale)[1]) {
      k <- sample(3, 1)
      if(k == 1){
        p = 1 / (1 + exp(-1 - X_scale[i, 1] - 2 * X_scale[i, 2] - 3 * X_scale[i, 3]))
        if(rbinom(1, 1, p) == 1)
          X[i, 4] <- NA
      }     
      if(k == 2){
        p = 1 / (1 + exp(-1 - X_scale[i, 1] - 2 * X_scale[i, 4]))
        if(rbinom(1, 1, p) == 1)
          X[i, 3] <- NA
      }
      if(k == 3){
        p = 1 / (1 + exp(-1 - X_scale[i, 1]))
        if(rbinom(1, 1, p) == 1)
          X[i, 5] <- NA
      }
    }
    #Generate missing data for Y|X
    for (i in 1:dim(Y_scale)[1]) {
      k <- sample(5, 1)
      if(k == 1){
        p = 1 / (1 + exp(-2 -X_scale[i, 1] - Y_scale[i, 8] - 3 * Y_scale[i, 9]))
        if(rbinom(1, 1, p) == 1)
          Y[i, c(2, 4)] <- NA
      } 
      if(k == 2){
        p = 1 / (1 + exp(-1 - X_scale[i, 2] - 3 * Y_scale[i, 4] + Y_scale[i, 6]))
        if(rbinom(1, 1, p) == 1)
          Y[i, 3] <- NA
      }
      if(k == 3){
        p = 1 / (1 + exp(-2 - 2 * Y_scale[i, 1] - 3 * Y_scale[i, 3] + Y_scale[i, 2]))
        if(rbinom(1, 1, p) == 1)
          Y[i, 7:9] <- NA
      }
      if(k == 4){
        p = 1 / (1 + exp(-1 - X_scale[i, 1] - X_scale[i, 2]))
        if(rbinom(1, 1, p) == 1)
          Y[i, c(1, 10)] <- NA
      }
      if(k == 5){
        p = 1 / (1 + exp(-1 - Y_scale[i, 1] - Y_scale[i, 10] - X_scale[i, 1] - X_scale[i, 2]))
        if(rbinom(1, 1, p) == 1)
          Y[i, 5:6] <- NA
      }
    }
    
    
    
    #-----------------------Set initial value of \theta---------------------
    bic_0 = Inf
    for (u in 1:dim(Y)[2]){
      mu_t <- rep(0, dim(X)[2])
      Sigma_x_t <- diag(dim(X)[2])
      beta_t <- matrix(rep(0, dim(Y)[2]*dim(X)[2]), nrow = dim(X)[2])
      Sigma_y_t <- diag(dim(Y)[2])
      #------------------------------env_em------------------------------------
      update_list <- update_par(X, Y, mu_t, Sigma_x_t, Sigma_y_t, beta_t, u)
      k = 0
      while (l1_norm(beta_t - update_list[[4]]) >0.001 & k < 50) {
        k = k+1
        mu_t <- update_list[[1]]
        Sigma_x_t <- update_list[[2]]
        Sigma_y_t <- update_list[[3]]
        beta_t <- update_list[[4]]
        Gamma_t <- update_list[[5]]
        update_list <- update_par(X, Y, mu_t, Sigma_x_t, Sigma_y_t, beta_t, u)
        print(l1_norm(beta_t - update_list[[4]]))
        
      }
      bic <- update_list[[6]]
      print(update_list[[7]])
      print(update_list[[8]])
      print(update_list[[9]])
      print(bic)
      print(sum((beta_t - beta)^2)/length(beta))
      if(bic < bic_0){
        bic_0 <- bic
        beta_t_min <- beta_t
        print(u)
      }
      else 
        break
    }
    if(k >= 999){
      print("Do not convergence!")
    }
    else{
      print("We choose envelope dimension")
      print(u-1)
      MSE_env_em <- c(sum((beta_t_min - beta)^2)/length(beta), MSE_env_em)
      print(sum((beta_t_min - beta)^2)/length(beta))
      print("This is loop")
      print(j)
      #complete case analysis:
      index <- unique(c(which(is.na(apply(X, 1, sum))), which(is.na(apply(Y, 1, sum)))))
      comp_X <- X[-index, ]
      comp_Y <- Y[-index, ]
      u.env_modified(comp_X, comp_Y)
      a <- env_modified(comp_X, comp_Y, 19)
      beta_comp_env <- t(a$beta)
      MSE_comp_env <- c(sum((beta_comp_env - beta)^2)/(p * q), MSE_comp_env)
      beta_comp_ols <- solve(t(comp_X) %*% comp_X) %*% t(comp_X) %*% comp_Y
      MSE_comp_ols <- c(sum((beta_comp_ols - beta)^2)/(p * q), MSE_comp_ols)
    }
  }, error=function(e){cat("ERROR :",conditionMessage(e), "\n")})
}
#write.csv("n = 1000, MAR, env_dim = 1", "MSE2_1.txt", quote = F, row.names = F)
#write.table("    env_em  comp_env  comp_ols", file = "MSE2_1.txt", append = T, col.names = F, quote = F, row.names = F)
#write.table(cbind(summary(MSE_env_em), summary(MSE_comp_env), summary(MSE_comp_ols)), file = "MSE2_1.txt", append = T, col.names = F)
#write.table(c(length(MSE_env_em), length(MSE_comp_env)), file = "MSE2_1.txt", append = T, col.names = F)

#print(MSE_lb)
#print(mean(MSE_env_em))
#print(mean(MSE_comp_env))

