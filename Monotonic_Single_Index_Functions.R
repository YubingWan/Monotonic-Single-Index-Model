##########################################################################################
## R-code for the following manuscript 
## "Monotonic Single-index Models with Application to Assessing Drug Interaction"
## by Yubing Wan, Susmita Datta and Maiying Kong
#############################################################################

###############################################################################
##  Form the jth M-spline basis function of order k for a vector z
##  Note: j+k <=length(knots)
############################################################################### 
library(MASS)
library(Matrix)
Mbasis <- function(z, k, j, knots, ...) {
       if(k == 1) {M <- ifelse(((z>=knots[j])&(z<knots[j+1])), 1/(knots[j+1]-knots[j]), 0)} 
       else {
            if(knots[j+k]==knots[j]) 
               alpha1 <- alpha2 <- 0 
            else 
               {alpha1 <- (k*(z-knots[j]))/((k-1)*(knots[j+k]-knots[j]))
               alpha2 <- (k*(knots[j+k]-z))/((k-1)*(knots[j+k]-knots[j]))
                }
               M <- alpha1*Mbasis(z, (k-1), j, knots)+alpha2*Mbasis(z, (k-1), (j+1), knots)
       }  
       return(M)
}


##################################################################################
###  Form a M-spline basis given z (a vector) and knots
##################################################################################
mbs <- function(z, k=3, knots) {
       knots<-sort(knots)
       n.knots<-length(knots)
       delta.L<-knots[2]-knots[1]
       delta.R<-knots[n.knots]-knots[n.knots-1]
       Sequence.knots <- c(knots[1]-((k-1):1)*delta.L, knots, knots[n.knots]+(1:(k-1))*delta.R)
       K <- n.knots+k-2
       M.mat <- matrix(0, length(z), K)
       for(j in 1:K) {M.mat[, j] <- Mbasis(z, k, j, Sequence.knots)}
       return(M.mat)
  }
##################################################################################
### Form cubic I-spline from cubic M splines (k+1=4) given index values z and knots
##################################################################################

ibs <- function(z, k=3, knots) {
       k1 <- k+1
       knots<-sort(knots)
       n.knots<-length(knots)
       delta.L<-knots[2]-knots[1]
       delta.R<-knots[n.knots]-knots[n.knots-1]
       t<-Sequence.knots <- c(knots[1]-(k:1)*delta.L, knots, knots[n.knots]+(1:k)*delta.R)     
       K <- n.knots+k-1        
       I.mat <- M.mat <- matrix(0, length(z), K)
       for(j in 1:K) {M.mat[, j] <- Mbasis(z, k1, j, Sequence.knots)} 
       for(l in k1:K) {        
           ind <- which(z >= t[l] & z < t[l+1])
           if (l==K) {ind <- which(z >= t[l])}
           if(l<K) {I.mat[ind, (l+1):K] <- 0}         
           for (j in (l-k+1):l){
                for (m in seq(j, l)){
                     I.mat[ind, j] <- I.mat[ind, j]+((t[m+k+1]-t[m])/(k+1))*M.mat[ind, m]
                }
           }
           I.mat[ind, 1:(l-k)] <- 1
       }
       ### k extra points at each end are added for additional knots for easy
       ### calculation, the foremost left ended basis function is removed.   
       return(I.mat[, -1])
}

##################################################################
###  The Penalty for the spline is beta*D*beta.
###  This function is used to calculate D matrix in the Penalty
##################################################################
##################################################################
###  The Penalty for the spline is beta*D*beta.
###  This function is used to calculate D matrix in the Penalty
##################################################################
PenD3 <- function (knots, k=3) {
         Bound.knots <- sort(knots)[c(1, length(knots))]
         Inter.knots <- sort(knots[which(knots!=Bound.knots[1] & knots!=Bound.knots[2])])
         dfL <- min(Bound.knots)- min(Inter.knots)
         dfU <- max(Bound.knots)- max(Inter.knots)
         L <- c(); for(i in 1:k) {L <- c(L, Bound.knots[1]+(i-1)*dfL)}
         U <- c(); for(i in 1:k) {U <- c(U, Bound.knots[2]+(i-1)*dfU)}
         t <- c(rev(L), Inter.knots, U)
         K <- length(t)
         a1 <-a2 <- a3 <- a4 <- c()
         for (j in 1:(K-k)) 
           {
            a1 <- c(a1, 6/((t[j+3]-t[j])*(t[j+2]-t[j]))) 
            a2 <- c(a2, (-6/(t[j+3]-t[j]))*(1/(t[j+2]-t[j])+1/(t[j+3]-t[j+1])))
            a3 <- c(a3, (3/(t[j+3]-t[j]))*((t[j+2]+t[j])/(t[j+2]-t[j])+
                                      (t[j+3]+t[j+1])/(t[j+3]-t[j+1]))) 
            a4 <- c(a4, 6/((t[j+3]-t[j])*(t[j+3]-t[j+1])))
           }         
         D <- matrix(rep(0, (K-k)*(K-k)), (K-k)) 
         for (j in 1:(K-k)){
             if (j==1)
               {
                D[j,j] <- a4[j]^2*(t[j+3]-t[j+2])/3
                D[j+1,j] <- D[j,j+1] <- -a4[j]*(a2[j+1]*(2*t[j+2]+t[j+3])+3*a3[j+1])/6
                D[j+2,j] <- D[j,j+2] <- -a4[j]*a1[j+2]*(t[j+3]-t[j+2])/6
               }
             if (j==2) 
                {
                D[j,j] <- (a2[j]^2*(t[j+2]^2+t[j+1]^2+t[j+2]*t[j+1])+
                          3*a2[j]*a3[j]*(t[j+2]+t[j+1])+3*a3[j]^2)/(3*(t[j+2]-t[j+1]))+
                            a4[j]^2*(t[j+3]-t[j+2])/3
                           D[j+1,j] <- D[j,j+1] <- a1[j+1]*(a2[j]*(2*t[j+2]+t[j+1])+3*a3[j])/6-
                                     a4[j]*(a2[j+1]*(2*t[j+2]+t[j+3])+3*a3[j+1])/6 
                D[j+2,j] <- D[j,j+2] <- -a4[j]*a1[j+2]*(t[j+3]-t[j+2])/6
                }
             if (j>2 & j<K-k-1) 
                {
                D[j,j] <- a1[j]^2*(t[j+1]-t[j])/3+(a2[j]^2*(t[j+2]^2+t[j+1]^2+t[j+2]*t[j+1])+
                          3*a2[j]*a3[j]*(t[j+2]+t[j+1])+3*a3[j]^2)/(3*(t[j+2]-t[j+1]))+
                          a4[j]^2*(t[j+3]-t[j+2])/3
                D[j+1,j] <- D[j,j+1] <- a1[j+1]*(a2[j]*(2*t[j+2]+t[j+1])+3*a3[j])/6-
                                           a4[j]*(a2[j+1]*(2*t[j+2]+t[j+3])+3*a3[j+1])/6
                D[j+2,j] <- D[j,j+2] <- -a4[j]*a1[j+2]*(t[j+3]-t[j+2])/6
                }
             if (j==K-k-1) 
                {   
                   D[j,j] <-a1[j]^2*(t[j+1]-t[j])/3+
                          (a2[j]^2*(t[j+2]^2+t[j+1]^2+t[j+2]*t[j+1])+
                          3*a2[j]*a3[j]*(t[j+2]+t[j+1])+3*a3[j]^2)/(3*(t[j+2]-t[j+1]))
                   D[j+1,j] <- D[j,j+1] <- a1[j+1]*(a2[j]*(2*t[j+2]+t[j+1])+3*a3[j])/6
                }
             if (j==K-k) 
                {
                   D[j,j] <- a1[j]^2*(t[j+1]-t[j])/3
                }
         }
         return(D)
}

#########################################################################################
### Objective function being minimized for estimating the link function f
#########################################################################################
objB <- function (beta,Y, imat, lambda, D,...) {  
         beta0  <- beta[1]  
         betaP  <- beta[-1] 
         f.hat  <- beta0+imat%*%betaP
         obj.beta <- mean((Y-f.hat)^2)+lambda*(t(betaP)%*%D%*%betaP)
         return(obj.beta)
}


##########################################################################################
###  Update alpha multiple times in the index given the fitted function f
##########################################################################################
Alpha1 <- function (X, Y, knots, k, beta, alpha.old, tol.alp, iter.alp, ...)
 {       # tol.alp is the tolerance error for convergence of alpha
         # iter.alp is the maximum iterated number for alpha given f
         n      <- dim(X)[1]
         alpha.old <- alpha.old/alpha.old[1]  
         Z         <- X%*%alpha.old      
         Dat       <- data.frame(Z=Z, Y=Y, X=X)
         Dat       <- Dat[order(Dat$Z), ]
         Z.s       <- Dat$Z
         Y.s       <- Dat$Y
         X.s       <- as.matrix(Dat[, -c(1, 2)])
         imat      <- ibs(z=Z.s, k=k, knots=knots)
         dmat      <- mbs(z=Z.s, k=k, knots=knots)
         f0        <- beta[1] + imat%*%beta[-1]       
         f.der     <- dmat%*%beta[-1] 
         X.star    <- diag(as.vector(f.der))%*%X.s[, -1]
         Y.star    <- Y.s - f0 + X.star%*%alpha.old[-1]      
         alphaT    <- ginv(t(X.star)%*%X.star)%*%t(X.star)%*%Y.star
         alpha     <- c(1, alphaT)
         tot.iter  <- 1
         while (max(abs(alpha-alpha.old)) > tol.alp && tot.iter <= iter.alp)
             {  
              alpha.old <- alpha
              Z         <- X%*%alpha.old 
              Dat       <- data.frame(Z=Z, Y=Y, X=X)
              Dat       <- Dat[order(Dat$Z), ]
              Z.s       <- Dat$Z
              Y.s       <- Dat$Y
              X.s       <- as.matrix(Dat[, -c(1, 2)])
              imat      <- ibs(z=Z.s, k=k, knots=knots)
              dmat      <- mbs(z=Z.s, k=k, knots=knots)
              f0        <- beta[1] + imat%*%beta[-1]       
              f.der     <- dmat%*%beta[-1]
              X.star    <- diag(as.vector(f.der))%*%X.s[, -1]
              Y.star    <- Y.s-f0 + X.star%*%alpha.old[-1]
              alphaT    <- ginv(t(X.star)%*%X.star)%*%t(X.star)%*%Y.star
              alpha     <- c(1, alphaT)
              tot.iter  <- tot.iter+1
            }
        Converge <- ifelse(tot.iter <= iter.alp, "YES", "NO")
        return(list(Converge=Converge, alpha=alpha)) 
}

#############################################################################
##  Algorithm for obtain parameters in single index model: both f and alpha  
##############################################################################
## Generate knots and put it in knot.s
##############################################################################

generate.knots<-function(Sindex, w0)
{   Z.u <- sort(unique(Sindex))
    s0 <- Z.u[1]                            
    knot.s <- s0
    for (j in 2:length(Z.u)) {
         if ((Z.u[j]-s0) >= w0) 
               {    s0 <- Z.u[j]
                    knot.s <- c(knot.s, s0)     
                } 
           }
    if (knot.s[length(knot.s)] < Z.u[length(Z.u)]) 
           { knot.s <- c(knot.s, Z.u[length(Z.u)]) }
    return(knot.s) 
}

######################################################################
## The main algorithm to estimate f and alpha iteratively
######################################################################
Est.f.alpha <- function(X, E, alpha.old, iter.lambda=50, iter.tot=200, 
      iter.alpha=30, crit.alpha=1e-4, d.knot=0.1, print=TRUE, ...) 
{ 
    N  <- length(E)
    alpha.old <- alpha.old
    k <- 3
    crit <- iter <- 1
    lam.temp <- GCV.temp <- c()
    beta.temp <- knot.temp <- as.list(1:iter.lambda)
    while (crit > crit.alpha && iter <= iter.tot) { 
        alpha.old <- alpha.old/alpha.old[1]              
        Z   <- X%*%alpha.old 
        Dat <- data.frame(Z=Z, E=E, X=X)
        Dat <- Dat[order(Dat$Z), ]   
        Z.s <- Dat$Z
        E.s <- Dat$E
        X.s <- as.matrix(Dat[, -c(1, 2)])
        Z.u <- unique(Z.s)
        if(iter <= iter.lambda) {
           knot.s<-generate.knots(Sindex=Z.u, w0=d.knot)
           knot.temp[[iter]] <- knot.s
           beta.old <- c(1, rep(1, (length(knot.s)+1)))
           B        <- length(beta.old)-1                                
           imat     <- ibs(z=Z.s, k=k, knots=knot.s)
           dmat     <- mbs(z=Z.s, k=k, knots=knot.s)
           PenM     <- PenD3(knot.s, k=k) 
           GCV <- beta.L <- c()  
           for (lam in lambdaL) {
                beta.obj <- nlminb(beta.old, objB, Y=E.s, imat=imat, lambda=lam, D=PenM, lower=c(-Inf, rep(0, B)))
                beta     <- as.numeric(beta.obj$par) 
                beta.L   <- cbind(beta.L, beta) 
                MSE      <- mean((E.s-(beta[1]+imat%*%beta[-1]))^2)
                S.lam    <- imat%*%ginv(t(imat)%*%imat+N*lam*PenM)%*%t(imat)
                GCV      <- c(GCV, MSE/(1-(1/N)*sum(diag(S.lam)))^2)
           }
           GCV.min   <- min(GCV)
           lam.min   <- lambdaL[which(GCV==GCV.min)]
           lam.temp  <- c(lam.temp, lam.min)
           GCV.temp  <- c(GCV.temp, GCV.min)
           beta.new  <- beta.L[, which(GCV==GCV.min)]
           beta.temp[[iter]] <- beta.new
         } else if(iter > iter.lambda) { 
             lam.min  <- mean(lam.temp[which(GCV.temp==min(GCV.temp))])
           # lam.min  <- lam.temp[iter.i]
           # beta.obj <- nlminb(beta.old, objB, Y=E.s, imat=imat, lambda=lam, D=PenM, lower=c(-Inf, rep(0, B)))
           # beta.new <- as.numeric(beta.obj$par) 
            Z   <- X%*%alpha.old 
            Dat <- data.frame(Z=Z, E=E, X=X)
            Dat <- Dat[order(Dat$Z), ]   
            Z.s <- Dat$Z
            E.s <- Dat$E
            X.s <- as.matrix(Dat[, -c(1, 2)])
            Z.u <- unique(Z.s)
            knot.s<-generate.knots(Sindex=Z.u, w0=d.knot)
           beta.old <- c(1, rep(1, (length(knot.s)+1)))
           B        <- length(beta.old)-1                                
           imat     <- ibs(z=Z.s, k=k, knots=knot.s)
           dmat     <- mbs(z=Z.s, k=k, knots=knot.s)
           PenM     <- PenD3(knot.s, k=k) 
           beta.obj <- nlminb(beta.old, objB, Y=E.s, imat=imat, lambda=lam.min, D=PenM, lower=c(-Inf, rep(0, B)))
           beta.new     <- as.numeric(beta.obj$par) 
          }   
        alpha.obj <- Alpha1(X.s, E.s, knot.s, k, beta.new, alpha.old, crit.alpha, iter.alpha)
        alpha.new <- alpha.obj$alpha
        Converge  <- alpha.obj$Converge    
        crit      <- max(abs(alpha.new-alpha.old))
        iter      <- iter+1 
        alpha.old <- alpha.new
        if(print) {
           print(list(Iter=iter, Crit=crit, Converge=Converge, Z=Z.u, Knot.S=knot.s, lamda=lam.min, alpha=alpha.new))
        }
    } 
    return(list(alpha=alpha.new, knots=knot.s, beta=beta.new, lambda=lam.min))      
}
##########################################################################
##          Sandwich variance estimate based on single index model
###########################################################################
 Calculate.Sandich.Variance<-function(X, E, lamda, knots, alpha.final, beta.final)  
    { Z      <- X%*%alpha.final
      Dat    <- data.frame(Z=Z, E=E, X=X) 
      Dat    <- Dat[order(Dat$Z), ] 
      Z.s    <- Dat$Z 
      E.s    <- Dat$E 
      X.s    <- as.matrix(Dat[, -c(1,2)])             
      imat1  <- ibs(z=Z.s, k=k, knots=knots)
      dmat1  <- mbs(z=Z.s, k=k, knots=knots)
      f.der  <- as.vector(dmat1%*%beta.final[-1]) 
      f.hat  <- as.vector(beta.final[1] + imat1%*%beta.final[-1])
      N<-nrow(X.s)
      n.alp<-length(alpha.final)-1
      n.beta<-length(beta.final)
      Imat<-cbind(rep(1, N), imat1)
      PenM     <- PenD3(knots, k=k)
      D.PenM   <- bdiag(0, PenM)
      Vmat  <- V.B <- V.M <-  matrix(0, n.alp+n.beta, n.alp+n.beta)
      V.B[1:n.alp,1:n.alp]<-t(X.s[, -1])%*%diag(f.der^2)%*%X.s[, -1]/N
      V.B[1:n.alp,(n.alp+1):(n.alp+n.beta)]<-t(X.s[, -1])%*%diag(f.der)%*%Imat/N
      V.B[(n.alp+1):(n.alp+n.beta), 1:n.alp]<-t(V.B[1:n.alp,(n.alp+1):(n.alp+n.beta)])
      V.B[(n.alp+1):(n.alp+n.beta), (n.alp+1):(n.alp+n.beta)]<-as.matrix(t(Imat)%*%Imat/N+lamda*D.PenM) 
      for (i in 1:nrow(X.s)) {phi<-c(as.vector(-(E.s[i]-f.hat[i])*f.der[i]*X.s[i, -1]), 
                                    as.vector(-(E.s[i]-f.hat[i])*Imat[i,]+lamda*D.PenM %*%beta.final))
                             V.M  <- V.M + phi%*%t(phi)
                            }
      Var.alp.beta <- (1/N)*ginv(V.B)%*%(V.M/N)%*%ginv(t(V.B))
      return( Var.alp.beta)
   }
##########################################################################
##          Predict the dose response surfaces and its standard errors
###########################################################################
Res.Surface <- function(D1, D2, k, alpha.f, knots, beta, Var.alpha.beta) 
     { a1 <- rep(1, length(D1))
       G  <- cbind(a1=a1, a2=sqrt(D1), a3=sqrt(D2), a4=D1, a5=D2, a6=sqrt(D1*D2))
       Com  <- diag(sqrt(D1*D2))%*%G
       X    <- cbind(D1, D2, Com)
       Z    <- X%*%alpha.f
       imat <- ibs(Z, k=k, knots=knots)
       dmat <- mbs(Z, k=k, knots=knots)
       y.pred   <- beta[1]+imat%*%beta[-1]
       df.dalp.t <- diag(as.vector(dmat%*%beta[-1]))%*%X[,-1]
       df.dbeta.t<-cbind(rep(1,length(imat[,1])), imat)
       A<-cbind(df.dalp.t, df.dbeta.t)
       Var.Pred.y<-A%*%Var.alpha.beta%*%t(A)
       SE.temp <- as.vector(sqrt(diag(Var.Pred.y)))
       return(list(Est=y.pred, SE=SE.temp, SI=Z))
     }
   
##########################################################################
##   Predict the interaction function g and its standard errors
###########################################################################
f.Synergy <- function(D1, D2, alpha.f, Var.alpha.beta) { 
       a0 <- rep(0, length(D1))
       a1 <- rep(1, length(D1))
       G  <- cbind(a0=a0, a1=a1, a2=sqrt(D1), a3=sqrt(D2), a4=D1, a5=D2, a6=sqrt(D1*D2))
       G.pred    <- G%*%alpha.f[-1]
       n.alp<-length(alpha.f)-1
       Var.Pred.G<-G%*%Var.alpha.beta[1:n.alp, 1:n.alp]%*%t(G)
       SE.temp <- as.vector(sqrt(diag(Var.Pred.G)))
       return(list(Est=G.pred, SE=SE.temp))
 }
      
