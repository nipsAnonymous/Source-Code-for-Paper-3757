# causal classification from data


library(igraph)
library(graph)
library(pcalg)
library(bnlearn)
library(RBGL)
library(stats)

strutRandDAG <- function(n = 100, n1 = 60, p1 = 0.1, k = 3, lB = 1.25, uB = 1.75, V = as.character(1:n)){
  # randomly sample a structured DAG
  # the DAG contains n nodes
  # n1 nodes are picked up to be equally divided into 3 classes, c1,c2,c3
  # the remaining nodes are randomly form a cpdag g
  # each of c1,c2,c3 is a chordal graph (may not fully connected), with p1 edge prob
  # chodal graphs have following super structure:
  # c1->c4, c2->c4, c3->c4, c4 is a chain comp of g
  # randomly choose k nodes from ci as a parent of each node in c_i+1
  
  rChordalGraph <- function(n, p){
    g <- sample_gnp(n, p)
    r <- is_chordal(g, newgraph = TRUE)
    g1 <- as_graphnel(r$newgraph)
    return(list(gnel = g1, gplot = r$newgraph))
  }
  
  amat <- matrix(0, n, n)
  m <- floor(n1/3)
  n2 <- n-n1
  
  randg <- pcalg::randomDAG(n2, p1, lB = 1.25, uB = 1.75, V = as.character((n1+1):n))
  randcpdag <- dag2cpdag(randg)
  tmpr <- divGraph(randcpdag)
  tmpug <- tmpr$ug
  cp <- connectedComp(tmpug)
  cn <- sample(1:length(cp),1)
  c4 <- cp[[cn]]
  
  for (i in 1:3){
    subg <- rChordalGraph(m, p1)[[1]]
    subm <- as(subg, 'matrix')
    amat[((i-1)*m+1):(i*m), ((i-1)*m+1):(i*m)] <- subm
    chosenNodes <- sample(((i-1)*m+1):(i*m),k)
    amat[chosenNodes, as.numeric(c4)] <- 1
  }
  
  amat[(n1+1):n, (n1+1):n] <- as(randcpdag, 'matrix')
  
  colnames(amat) <- V
  rownames(amat) <- V
  
  cpdag <- as(amat, 'graphNEL')
  dag <- pcalg::pdag2dag(cpdag, keepVstruct=TRUE)
  ndag <- weightAndSort(dag$graph, lB, uB)
  ncpdag <- pcalg::dag2cpdag(ndag)
  return(list(dag = ndag, cpdag = ncpdag))  
  
}

criticalSet <- function(g, x, z){
  
  # given a chordal graph g, g may be disconnected
  # find the critical set of x w.r.t z
  # g is a graphNEL object
  # x is a number, z is an array
  
  n <- length(g@nodes)
  S <- list(c(x, 0, 0))
  C <- matrix(0, 1, n)
  flag <- 1
  dlp <- 0
  while (length(S) != 0){
    dlp <- dlp +1
    e <- S[[1]]
    S[[1]] <- NULL
    if (sum(z == e[1])==0 && e[2] != 0){
      for (alpha in setdiff(g@edgeL[[e[1]]][[1]],e[2])){
        if (sum(g@edgeL[[e[2]]][[1]]==alpha)==0){
          if (e[2] == x){
            S[[length(S)+1]] <- c(alpha, e[1], e[1])
          }else{
            S[[length(S)+1]] <- c(alpha, e[1], e[3])
          }
        }
      }
    }else if (sum(z == e[1])==0){
      for (alpha in g@edgeL[[e[1]]][[1]]){
        S[[length(S)+1]] <- c(alpha, e[1], alpha)
      }
    }else {
      C[flag] <- e[3]
      flag <- flag + 1
    }
    # if chordless cycle presents, then the while loop wil never end
    # DEAD loop prevent
    if (dlp > (n^2+1)) break
  }
  C <- unique(C[C!=0])
  return(C)
}

divGraph <- function(cpdag){
  
  # given a cpdag, this function divides it into undir subg and dir subg
  # cpdag is a graphNEL obj
  
  mat <- as(cpdag, 'matrix')
  dirmat <- mat
  udirmat <- mat
  
  dirmat[(mat-t(mat))==0] <- 0
  dirG <- as(dirmat, 'graphNEL')
  
  udirmat[mat==1 & t(mat)==0] <- 0
  udirG <- as(udirmat, 'graphNEL')
  
  return(list(dg = dirG, ug = udirG))
}

causalType <- function(cpdag){
  
  # RES is a matrix, 
  # -1 means undetermined, 
  # 0 means no cause, 
  # 1 means potential cause, 
  # 2 means trivial inv
  # 3 means non-trivial inv
  
  div <- divGraph(cpdag)
  dgm <- as(div$dg, 'matrix')
  ugm <- as(div$ug, 'matrix')
  
  tmpDgm <- dgm
  tmpUgm <- ugm
  
  if (length(cpdag@nodes) >= 2){
    for (i in 2:length(cpdag@nodes)){
      tmpDgm <- dgm + tmpDgm%*%dgm
      tmpUgm <- ugm + tmpUgm%*%ugm
    }
  }
  
  res <- matrix(-1, length(cpdag@nodes), length(cpdag@nodes))
  
  res[tmpDgm > 0] <- 2 
  res[tmpUgm > 0] <- 1
  
  for (x in 1:length(cpdag@nodes)){
    for (y in 1:length(cpdag@nodes)){
      if (x != y & res[x, y] == -1){
        # print(c(x,y))
        z <- which(res[,y] == 2, arr.ind = TRUE)
        C <- criticalSet(div$ug, x, z)
        sub <- ugm[C, C]
        if (length(C) == 0){
          res[x, y] <- 0
        }else if (sum(sub+diag(1,length(C), length(C)) != 1)==0){
          res[x, y] <- 1
        }else{
          res[x, y] <- 3
        }
      }
      else if (x == y){
        res[x, y] <- -1
      }
    }
  }
  return(res)
}

compGraphs <- function(g, gt){
  r1 <- pcalg::shd(g, gt)
  r <- pcalg::compareGraphs(g, gt)
  return(c(shd = r1, r))
}

compareClusters <- function(rc, tc){
  # compute confusion matrix
  cmat <- matrix(0, 4, 4)
  # col:predicted row:truth
  for (i in 1:length(rc)){
    cmat[tc[i]+1, rc[i]+1] <- cmat[tc[i]+1, rc[i]+1] + 1
  }
  r <- matrix(0, 4, 4)
  colnames(r) <- c('precision', 'recall', 'F1', 'FPR')
  for (i in 1:4){
    r[i, 1] <- if (is.nan(cmat[i,i]/sum(cmat[i, ]))) 1 else cmat[i,i]/sum(cmat[i, ])
    r[i, 2] <- if (is.nan(cmat[i,i]/sum(cmat[, i]))) 1 else cmat[i,i]/sum(cmat[, i])
    r[i, 3] <- if (is.nan(2*r[i, 1]*r[i, 2]/(r[i, 1] + r[i, 2]))) 0 else 2*r[i, 1]*r[i, 2]/(r[i, 1] + r[i, 2])
    r[i, 4] <- if (is.nan(sum(cmat[-i,i])/sum(cmat[-i,]))) 0 else sum(cmat[-i,i])/sum(cmat[-i,])
  }
  Fscore <- (sum(cmat[1, ])*r[1, 3]+sum(cmat[2, ])*r[2, 3]+
               sum(cmat[3, ])*r[3, 3]+sum(cmat[4, ])*r[4, 3])/sum(cmat)
  Ave.TPR <- (sum(cmat[1, ])*r[1, 1]+sum(cmat[2, ])*r[2, 1]+
                sum(cmat[3, ])*r[3, 1]+sum(cmat[4, ])*r[4, 1])/sum(cmat)
  Ave.FPR <- (sum(cmat[1, ])*r[1, 4]+sum(cmat[2, ])*r[2, 4]+
                sum(cmat[3, ])*r[3, 4]+sum(cmat[4, ])*r[4, 4])/sum(cmat)
  return(c(Fscore = Fscore, Ave.TPR =Ave.TPR, Ave.FPR =Ave.FPR))
}

compareCMat <- function(res, rest){
  rc <- as.vector(res)
  rt <- as.vector(rest)
  rc <- rc[-which(rc==-1)]
  rt <- rt[-which(rt==-1)]
  R <- compareClusters(rc, rt)
  
  tpr0 <- sum(rc==0 & rt==0)/(sum(rc==0 & rt==0)+sum(rc!=0 & rt==0))
  if (is.nan(tpr0)) tpr0 <- 1 
  fpr0 <- sum(rc==0 & rt!=0)/(sum(rc==0 & rt!=0)+sum(rc!=0 & rt!=0))
  if (is.nan(fpr0)) fpr0 <- 0 
  
  tpr1 <- sum(rc==1 & rt==1)/(sum(rc==1 & rt==1)+sum(rc!=1 & rt==1))
  if (is.nan(tpr1)) tpr1 <- 1 
  fpr1 <- sum(rc==1 & rt!=1)/(sum(rc==1 & rt!=1)+sum(rc!=1 & rt!=1))
  if (is.nan(fpr1)) fpr1 <- 0 
  
  tpr2 <- sum(rc==2 & rt==2)/(sum(rc==2 & rt==2)+sum(rc!=2 & rt==2))
  if (is.nan(tpr2)) tpr2 <- 1 
  fpr2 <- sum(rc==2 & rt!=2)/(sum(rc==2 & rt!=2)+sum(rc!=2 & rt!=2))
  if (is.nan(fpr2)) fpr2 <- 0 
  
  tpr3 <- sum(rc==3 & rt==3)/(sum(rc==3 & rt==3)+sum(rc!=3 & rt==3))
  if (is.nan(tpr3)) tpr3 <- 1 
  fpr3 <- sum(rc==3 & rt!=3)/(sum(rc==3 & rt!=3)+sum(rc!=3 & rt!=3))
  if (is.nan(fpr3)) fpr3 <- 0
  
  return(c(R, tpr0 = tpr0, fpr0 = fpr0
           , tpr1 = tpr1, fpr1 = fpr1
           , tpr2 = tpr2, fpr2 = fpr2
           , tpr3 = tpr3, fpr3 = fpr3))
}

computeConfMat <- function(res, rest){
  rc <- as.vector(res)
  rt <- as.vector(rest)
  rc <- rc[-which(rc==-1)]
  rt <- rt[-which(rt==-1)]
  # compute confusion matrix
  cmat <- matrix(0, 4, 4)
  # col:predicted row:truth
  for (i in 1:length(rc)){
    cmat[rt[i]+1, rc[i]+1] <- cmat[rt[i]+1, rc[i]+1] + 1
  }
  b <- c('pred_nc', 'pred_ni', 'pred_ci', 'pred_si')
  a <- c('true_nc', 'true_ni', 'true_ci', 'true_si')
  # return a vector, to recover the original matrix, use matrix(vec, 4,4)
  c <- as.vector(outer(a,b,paste))
  rrr <- as.vector(cmat)
  names(rrr) <- c
  return(rrr)
}

evaluationFromCmat <- function(cmat){

  tpr0 <- cmat[1,1]/sum(cmat[1,])
  if (is.nan(tpr0)) tpr0 <- 1 
  fpr0 <-sum(cmat[2:4,1])/sum(cmat[2:4,])
  if (is.nan(fpr0)) fpr0 <- 0 
  
  tpr1 <- cmat[2,2]/sum(cmat[2,])
  if (is.nan(tpr1)) tpr1 <- 1 
  fpr1 <-sum(cmat[c(1,3,4),2])/sum(cmat[c(1,3,4),])
  if (is.nan(fpr1)) fpr1 <- 0 
  
  tpr2 <- cmat[3,3]/sum(cmat[3,])
  if (is.nan(tpr2)) tpr2 <- 1 
  fpr2 <-sum(cmat[c(1,2,4),3])/sum(cmat[c(1,2,4),])
  if (is.nan(fpr2)) fpr2 <- 0 
  
  tpr3 <- cmat[4,4]/sum(cmat[4,])
  if (is.nan(tpr3)) tpr3 <- 1 
  fpr3 <-sum(cmat[c(1,2,3),4])/sum(cmat[c(1,2,3),])
  if (is.nan(fpr3)) fpr3 <- 0 
  
  return(c(tpr0 = tpr0, fpr0 = fpr0, tpr1 = tpr1, fpr1 = fpr1, tpr2 = tpr2, fpr2 = fpr2, tpr3 = tpr3, fpr3 = fpr3))
}

evaluationFromCmat_ac <- function(cmat, alpha){
  
  ad <- qnorm(p = 1-alpha/2)^2
  
  tpr0 <- (cmat[1,1]+ad/2)/(sum(cmat[1,])+ad)
  var_tpr_0 <- tpr0*(1-tpr0)/(sum(cmat[1,])+ad)
  if (is.nan(tpr0)){
    tpr0 <- 1
    var_tpr_0 <- 0}
  fpr0 <-(sum(cmat[2:4,1])+ad/2)/(sum(cmat[2:4,])+ad)
  var_fpr_0 <- fpr0*(1-fpr0)/(sum(cmat[2:4,])+ad)
  if (is.nan(fpr0)) fpr0 <- var_tpr_0 <- 0 
  
  tpr1 <- (cmat[2,2]+ad/2)/(sum(cmat[2,])+ad)
  var_tpr_1 <- tpr1*(1-tpr1)/(sum(cmat[2,])+ad)
  if (is.nan(tpr1)){
    tpr1 <- 1
    var_tpr_1 <- 0}
  fpr1 <-(sum(cmat[c(1,3,4),2])+ad/2)/(sum(cmat[c(1,3,4),])+ad)
  var_fpr_1 <- fpr1*(1-fpr1)/(sum(cmat[c(1,3,4),])+ad)
  if (is.nan(fpr1)) fpr1 <- var_fpr_1 <- 0 
  
  tpr2 <- (cmat[3,3]+ad/2)/(sum(cmat[3,])+ad)
  var_tpr_2 <- tpr2*(1-tpr2)/(sum(cmat[3,])+ad)
  if (is.nan(tpr2)){
    tpr2 <- 1 
    var_tpr_2 <- 0}
  fpr2 <-(sum(cmat[c(1,2,4),3])+ad/2)/(sum(cmat[c(1,2,4),])+ad)
  var_fpr_2 <- fpr2*(1-fpr2)/(sum(cmat[c(1,2,4),])+ad)
  if (is.nan(fpr2)) fpr2 <- var_fpr_2 <- 0 
  
  tpr3 <- (cmat[4,4]+ad/2)/(sum(cmat[4,])+ad)
  var_tpr_3 <- tpr3*(1-tpr3)/(sum(cmat[4,])+ad)
  if (is.nan(tpr3)) {
    tpr3 <- 1
    var_tpr_3 <- 0}
  fpr3 <-(sum(cmat[c(1,2,3),4])+ad/2)/(sum(cmat[c(1,2,3),])+ad)
  var_fpr_3 <- fpr3*(1-fpr3)/(sum(cmat[c(1,2,3),])+ad)
  if (is.nan(fpr3)) fpr3 <- var_fpr_3 <- 0 
  
  return(c(tpr0 = tpr0, fpr0 = fpr0, tpr1 = tpr1, fpr1 = fpr1, tpr2 = tpr2, fpr2 = fpr2, tpr3 = tpr3, fpr3 = fpr3,
           var_tpr_0 = var_tpr_0, var_fpr_0 = var_fpr_0, var_tpr_1 = var_tpr_1, var_fpr_1 = var_fpr_1,
           var_tpr_2 = var_tpr_2, var_fpr_2 = var_fpr_2, var_tpr_3 = var_tpr_3, var_fpr_3 = var_fpr_3))
}


evaluation <- function(r){
  t <- r[,ncol(r)]
  s <- r[,-ncol(r)]
  
  ave_time <- mean(t)
  sd_t <- sd(t)
  
  cmat <- matrix(colSums(s),4,4)
  
  res1 <- evaluationFromCmat(cmat)
  
  res <- evaluationFromCmat_ac(cmat, 0.05)
  
  return(c(res1[1:8], res[9:16], ave_time = ave_time, sd_t))
}

orientation <- function(G, sepset){
  
  # define meek's rules
  rule1 <- function(pdag, sepset) {
    search.pdag <- pdag
    ind <- which(pdag == 1 & t(pdag) == 0, arr.ind = TRUE)
    for (i in seq_len(nrow(ind))) {
      # a -> b
      a <- ind[i, 1]
      b <- ind[i, 2]
      isC <- which(search.pdag[b, ] == 1 & search.pdag[, b] == 1 
                   & search.pdag[a, ] == 0 & search.pdag[, a] == 0)
      if (length(isC) > 0) {
        for (ii in seq_along(isC)) {
          c <- isC[ii]
          
          if (b %in% sepset[[a]][[c]] || b %in% sepset[[c]][[a]]){
            pdag[b, c] <- 1
            pdag[c, b] <- 0
          }
          
        }
      }
      search.pdag <- pdag
    }
    pdag
  }
  rule2 <- function(pdag, sepset) {
    search.pdag <- pdag
    ind <- which(search.pdag == 1 & t(search.pdag) == 1, 
                 arr.ind = TRUE)
    for (i in seq_len(nrow(ind))) {
      a <- ind[i, 1]
      b <- ind[i, 2]
      isC <- which(search.pdag[a, ] == 1 & search.pdag[, a] == 0 
                   & search.pdag[, b] == 1 & search.pdag[b, ] == 0)
      for (ii in seq_along(isC)) {
        c <- isC[ii]
        pdag[a, b] <- 1
        pdag[b, a] <- 0
      }
      search.pdag <- pdag
    }
    pdag
  }
  rule3 <- function(pdag, sepset) {
    search.pdag <- pdag
    ind <- which(search.pdag == 1 & t(search.pdag) == 1, 
                 arr.ind = TRUE)
    for (i in seq_len(nrow(ind))) {
      a <- ind[i, 1]
      b <- ind[i, 2]
      c <- which(search.pdag[a, ] == 1 & search.pdag[, 
                                                     a] == 1 & search.pdag[, b] == 1 & search.pdag[b, 
                                                                                                   ] == 0)
      if (length(c) >= 2) {
        cmb.C <- combn(c, 2)
        cC1 <- cmb.C[1, ]
        cC2 <- cmb.C[2, ]
        for (j in seq_along(cC1)) {
          c1 <- cC1[j]
          c2 <- cC2[j]
          if (search.pdag[c1, c2] == 0 && search.pdag[c2, c1] == 0) {
            if (a %in% sepset[[c1]][[c2]] || a %in% sepset[[c2]][[c1]]){
              pdag[a, b] <- 1
              pdag[b, a] <- 0
              search.pdag <- pdag
              break
            }
          }
        }
      }
    }
    pdag
  }
  
  pdag <- G
  p <- nrow(pdag)
  repeat {
    old_pdag <- pdag
    pdag <- rule1(pdag, sepset)
    pdag <- rule2(pdag, sepset)
    pdag <- rule3(pdag, sepset)
    if (all(pdag == old_pdag)) 
      break
  }
  pdag
}

rmvNodes <- function(t, waitList, G){
  # for each node in waitList, if it has a undirected path with t, keep it in the list, otherwise delete it
  canV <- c(t)
  for (i in 1:length(waitList)){
    ind <- which(G[, canV] == 1 & t(G[canV, ]) == 1, arr.ind = TRUE)
    if (length(canV)==1){
      tmp <- unique(ind[, 2])
    }else{
      tmp <- unique(ind[, 1])
    }
    A <- union(canV, tmp)
    canV <- A
  }
  res <- intersect(waitList, canV)
  return(res)
}

mb_by_mb_self <- function(t, data, alpha, indepTest, sig = 'gauss'){
  
  # initialization
  n <- ncol(data)
  varNames <- colnames(data)
  colnames(data) <- 1:n
  doneList <- c()
  waitList <- c(t)
  MG <- matrix(0, n, n)
  G <- matrix(0, n, n)
  sepset <- lapply(1:n, function(.) vector("list", n))
  
  if (sig == 'dis'){
    tlev <- matrix(0, 1, n)
    for  (i in 1:n){
      tlev[i] <- length(levels(data[, i]))
      data[,i] <- as.numeric(data[,i])
    }
    data <- data - 1
    tsuffStat <- list(dm = data, nlev = tlev, adaptDF = FALSE)
  }else{
    tsuffStat = list(C = cor(data), n = nrow(data))
  }
  
  numtests <- 0
  
  while (length(waitList) != 0){
    # print(waitList)
    x <- waitList[1]
    waitList <- waitList[-1]
    R <- iamb.forward(x, n, tsuffStat, alpha, indepTest)
    mbx <- R[[1]]
    numtests <- numtests + R[[2]]
    if (length(mbx)==0){
      break
    }
    waitList <- append(waitList, setdiff(setdiff(mbx, doneList), waitList))
    doneList <- append(doneList, x)
    
    # record sepset between x and variabls out of mbx
    A <- setdiff(setdiff(1:n,x),mbx)
    for (i in A){
      sepset[[x]][[i]] <- sepset[[i]][[x]] <- mbx
    }
    
    
    marginalData <- data[, c(x, mbx)]
    
    if (sig == 'dis'){
      lev <- tlev[, c(x, mbx)]
      suffStat <- list(dm = marginalData, nlev = lev, adaptDF = FALSE)
    }else{
      suffStat = list(C = cor(marginalData), n = nrow(marginalData))
    }
    
    p <- length(c(x, mbx))
    
    # learning local graph based on pc
    # only learn the skel and orient v-structures
    skel <- pcalg::skeleton(suffStat, indepTest, alpha, as.character(c(x, mbx)), method = 'original') 
    numtests <- numtests + sum(skel@n.edgetests)
    lx <- udag2pdagRelaxed(skel, orientCollider = TRUE, rules = rep(FALSE, 3))
    localMat <- as(lx@graph, 'matrix')
    subG <- matrix(0, p, p)
    for (i in 2:p){
      if (localMat[i, 1] == 1 & localMat[1, i] == 1){
        subG[i, 1] <- subG[1, i] <- 1
      }else if (localMat[i, 1] == 1 & localMat[1, i] == 0){
        subG[i, 1] <- 1
        subG[1, i] <- 0
      }else if (localMat[i, 1] == 0 & localMat[1, i] == 1){
        subG[i, 1] <- 0
        subG[1, i] <- 1
        # for every node pointed at i but not adjacent to 1
        cop <- which(localMat[, i] == 1 & localMat[i, ] == 0 
                     & localMat[1, ] == 0 & localMat[, 1] == 0)
        for (j in cop){
          subG[j, i] <- 1
          subG[i, j] <- 0
        }
      }
    }
    
    # when a conflict ocurrs
    # a former directed edge will not be changed 
    # a former undiredcted will be changed as a new directed edge
    # the indept relations appear in marginal P are also appear in joint P
    # transform local sepsets into global ones
    subNames <- as.numeric(c(x, mbx))
    for (i in 1:(p-1)){
      for (j in (i+1):p){
        
        if (subG[i, j] == 1 & subG[j, i] == 1){
          if (G[subNames[i], subNames[j]] == 0 & G[subNames[j], subNames[i]] == 0) 
            G[subNames[i], subNames[j]] <- G[subNames[j], subNames[i]] <- 1
        }else if (subG[i, j] == 1 & subG[j, i] == 0){
          if (!(G[subNames[i], subNames[j]] == 0 & G[subNames[j], subNames[i]] == 1)){
            G[subNames[i], subNames[j]] <- 1
            G[subNames[j], subNames[i]] <- 0
          }
        }else if (subG[i, j] == 0 & subG[j, i] == 1){
          if (!(G[subNames[i], subNames[j]] == 1 & G[subNames[j], subNames[i]] == 0)){
            G[subNames[i], subNames[j]] <- 0
            G[subNames[j], subNames[i]] <- 1
          }
        }else{
          sepset[[subNames[i]]][[subNames[j]]] <- sepset[[subNames[j]]][[subNames[i]]] <- subNames[skel@sepset[[i]][[j]]]
        }
        
      }
    }
    
    G <- orientation(G, sepset)
    # colnames(G) <- varNames
    # rownames(G) <- varNames
    
    waitList <- rmvNodes(t, waitList, G)
    
  }
  res <- as(G, 'graphNEL')
  return(list(res, numtests))
}

mb_by_mb_self_ORACLE <- function(t, tdag){
  
  # initialization
  indepTest <- gaussCItest
  alpha <- 0.99999999
  n <- length(tdag@nodes)
  varNames <- tdag@nodes

  doneList <- c()
  waitList <- c(t)
  MG <- matrix(0, n, n)
  G <- matrix(0, n, n)
  sepset <- lapply(1:n, function(.) vector("list", n))
  
  cov.mat <- trueCov(tdag)
  true.corr <- cov2cor(cov.mat)
  tsuffStat = list(C = true.corr, n = 10^9)

  while (length(waitList) != 0){
    # print(waitList)
    x <- waitList[1]
    waitList <- waitList[-1]
    mbx <- iamb.forward(x, n, tsuffStat, alpha, indepTest)[[1]]
    waitList <- append(waitList, setdiff(setdiff(mbx, doneList), waitList))
    doneList <- append(doneList, x)
    
    # record sepset between x and variabls out of mbx
    A <- setdiff(setdiff(1:n,x),mbx)
    for (i in A){
      sepset[[x]][[i]] <- sepset[[i]][[x]] <- mbx
    }
    
    
    subNodes <- c(x, mbx)
    marginalCorr <- matrix(0, length(subNodes), length(subNodes))
    for (i in 1:length(subNodes)){
      for (j in 1:length(subNodes)){
        if (i == j){
          marginalCorr[i, j] <- 1
        }else{
          marginalCorr[i, j] <- true.corr[subNodes[i], subNodes[j]]
        }
      }
    }
    colnames(marginalCorr) <- subNodes
    rownames(marginalCorr) <- subNodes

    suffStat = list(C = marginalCorr, n = 10^9)

    
    p <- length(c(x, mbx))
    
    # learning local graph based on pc
    # only learn the skel and orient v-structures
    skel <- pcalg::skeleton(suffStat, indepTest, alpha, as.character(c(x, mbx)), method = 'original') 
    lx <- udag2pdagRelaxed(skel, orientCollider = TRUE, rules = rep(FALSE, 3))
    localMat <- as(lx@graph, 'matrix')
    subG <- matrix(0, p, p)
    for (i in 2:p){
      if (localMat[i, 1] == 1 & localMat[1, i] == 1){
        subG[i, 1] <- subG[1, i] <- 1
      }else if (localMat[i, 1] == 1 & localMat[1, i] == 0){
        subG[i, 1] <- 1
        subG[1, i] <- 0
      }else if (localMat[i, 1] == 0 & localMat[1, i] == 1){
        subG[i, 1] <- 0
        subG[1, i] <- 1
        # for every node pointed at i but not adjacent to 1
        cop <- which(localMat[, i] == 1 & localMat[i, ] == 0 
                     & localMat[1, ] == 0 & localMat[, 1] == 0)
        for (j in cop){
          subG[j, i] <- 1
          subG[i, j] <- 0
        }
      }
    }
    
    # when a conflict ocurrs
    # a former directed edge will not be changed 
    # a former undiredcted will be changed as a new directed edge
    # the indept relations appear in marginal P are also appear in joint P
    # transform local sepsets into global ones
    subNames <- as.numeric(c(x, mbx))
    for (i in 1:(p-1)){
      for (j in (i+1):p){
        
        if (subG[i, j] == 1 & subG[j, i] == 1){
          if (G[subNames[i], subNames[j]] == 0 & G[subNames[j], subNames[i]] == 0) 
            G[subNames[i], subNames[j]] <- G[subNames[j], subNames[i]] <- 1
        }else if (subG[i, j] == 1 & subG[j, i] == 0){
          if (!(G[subNames[i], subNames[j]] == 0 & G[subNames[j], subNames[i]] == 1)){
            G[subNames[i], subNames[j]] <- 1
            G[subNames[j], subNames[i]] <- 0
          }
        }else if (subG[i, j] == 0 & subG[j, i] == 1){
          if (!(G[subNames[i], subNames[j]] == 1 & G[subNames[j], subNames[i]] == 0)){
            G[subNames[i], subNames[j]] <- 0
            G[subNames[j], subNames[i]] <- 1
          }
        }else{
          sepset[[subNames[i]]][[subNames[j]]] <- sepset[[subNames[j]]][[subNames[i]]] <- subNames[skel@sepset[[i]][[j]]]
        }
        
      }
    }
    
    G <- orientation(G, sepset)
    # colnames(G) <- varNames
    # rownames(G) <- varNames
    
    waitList <- rmvNodes(t, waitList, G)
    
  }
  res <- as(G, 'graphNEL')
  return(res)
}

mb_by_mb_self_ORACLE_modify <- function(t, tdag){
  
  # initialization
  indepTest <- gaussCItest
  alpha <- 0.9999999
  n <- length(tdag@nodes)
  varNames <- tdag@nodes
  
  doneList <- c()
  waitList <- c(t)
  MG <- matrix(0, n, n)
  G <- matrix(0, n, n)
  sepset <- lapply(1:n, function(.) vector("list", n))
  
  cov.mat <- trueCov(tdag)
  true.corr <- cov2cor(cov.mat)
  tsuffStat = list(C = true.corr, n = 10^9)
  
  while (length(waitList) != 0){
    print(waitList)
    x <- waitList[1]
    waitList <- waitList[-1]
    mbx <- iamb.forward(x, n, tsuffStat, alpha, indepTest)[[1]]
    waitList <- append(waitList, setdiff(setdiff(mbx, doneList), waitList))
    doneList <- append(doneList, x)
    
    # record sepset between x and variabls out of mbx
    A <- setdiff(setdiff(1:n,x),mbx)
    for (i in A){
      sepset[[x]][[i]] <- sepset[[i]][[x]] <- mbx
    }
    
    
    subNodes <- c(x, mbx)
    marginalCorr <- matrix(0, length(subNodes), length(subNodes))
    for (i in 1:length(subNodes)){
      for (j in 1:length(subNodes)){
        if (i == j){
          marginalCorr[i, j] <- 1
        }else{
          marginalCorr[i, j] <- true.corr[subNodes[i], subNodes[j]]
        }
      }
    }
    colnames(marginalCorr) <- subNodes
    rownames(marginalCorr) <- subNodes
    
    suffStat = list(C = marginalCorr, n = 10^9)
    
    
    p <- length(c(x, mbx))
    
    # learning local graph based on pc
    # only learn the skel and orient v-structures
    skel <- pcalg::skeleton(suffStat, indepTest, alpha, as.character(c(x, mbx)), method = 'original') 
    lx <- udag2pdagRelaxed(skel, orientCollider = TRUE, rules = rep(FALSE, 3))
    localMat <- as(lx@graph, 'matrix')
    subG <- matrix(0, p, p)
    for (i in 2:p){
      if (localMat[i, 1] == 1 & localMat[1, i] == 1){
        subG[i, 1] <- subG[1, i] <- 1
      }else if (localMat[i, 1] == 1 & localMat[1, i] == 0){
        subG[i, 1] <- 1
        subG[1, i] <- 0
      }
      else if (localMat[i, 1] == 0 & localMat[1, i] == 1){
        subG[i, 1] <- 1
        subG[1, i] <- 1
        # # for every node pointed at i but not adjacent to 1
        # cop <- which(localMat[, i] == 1 & localMat[i, ] == 0
        #              & localMat[1, ] == 0 & localMat[, 1] == 0)
        # for (j in cop){
        #   subG[j, i] <- 1
        #   subG[i, j] <- 0
        # }
      }
    }
    
    # when a conflict ocurrs
    # a former directed edge will not be changed 
    # a former undiredcted will be changed as a new directed edge
    # the indept relations appear in marginal P are also appear in joint P
    # transform local sepsets into global ones
    subNames <- as.numeric(c(x, mbx))
    for (i in 1:(p-1)){
      for (j in (i+1):p){
        
        if (subG[i, j] == 1 & subG[j, i] == 1){
          if (G[subNames[i], subNames[j]] == 0 & G[subNames[j], subNames[i]] == 0) 
            G[subNames[i], subNames[j]] <- G[subNames[j], subNames[i]] <- 1
        }else if (subG[i, j] == 1 & subG[j, i] == 0){
          if (!(G[subNames[i], subNames[j]] == 0 & G[subNames[j], subNames[i]] == 1)){
            G[subNames[i], subNames[j]] <- 1
            G[subNames[j], subNames[i]] <- 0
          }
        }else if (subG[i, j] == 0 & subG[j, i] == 1){
          if (!(G[subNames[i], subNames[j]] == 1 & G[subNames[j], subNames[i]] == 0)){
            G[subNames[i], subNames[j]] <- 0
            G[subNames[j], subNames[i]] <- 1
          }
        }else{
          sepset[[subNames[i]]][[subNames[j]]] <- sepset[[subNames[j]]][[subNames[i]]] <- subNames[skel@sepset[[i]][[j]]]
        }
        
      }
    }
    
    G <- orientation(G, sepset)
    # colnames(G) <- varNames
    # rownames(G) <- varNames
    
    waitList <- rmvNodes(t, waitList, G)
    
  }
  res <- as(G, 'graphNEL')
  return(res)
}

mb_by_mb_self_modify <- function(t, data, alpha, indepTest, sig = 'gauss'){
  
  # initialization
  n <- ncol(data)
  varNames <- colnames(data)
  colnames(data) <- 1:n
  doneList <- c()
  waitList <- c(t)
  MG <- matrix(0, n, n)
  G <- matrix(0, n, n)
  sepset <- lapply(1:n, function(.) vector("list", n))
  
  if (sig == 'dis'){
    tlev <- matrix(0, 1, n)
    for  (i in 1:n){
      tlev[i] <- length(levels(data[, i]))
      data[,i] <- as.numeric(data[,i])
    }
    data <- data - 1
    tsuffStat <- list(dm = data, nlev = tlev, adaptDF = FALSE)
  }else{
    tsuffStat = list(C = cor(data), n = nrow(data))
  }
  
  numtests <- 0
  
  while (length(waitList) != 0){
    # print(waitList)
    x <- waitList[1]
    waitList <- waitList[-1]
    R <- iamb.forward(x, n, tsuffStat, alpha, indepTest)
    mbx <- R[[1]]
    if (length(mbx)==0){
      break
    }
    numtests <- numtests + R[[2]]
    waitList <- append(waitList, setdiff(setdiff(mbx, doneList), waitList))
    doneList <- append(doneList, x)
    
    # record sepset between x and variabls out of mbx
    A <- setdiff(setdiff(1:n,x),mbx)
    for (i in A){
      sepset[[x]][[i]] <- sepset[[i]][[x]] <- mbx
    }
    
    
    marginalData <- data[, c(x, mbx)]
    if (sig == 'dis'){
      lev <- tlev[, c(x, mbx)]
      suffStat <- list(dm = marginalData, nlev = lev, adaptDF = FALSE)
    }else{
      suffStat = list(C = cor(marginalData), n = nrow(marginalData))
    }
    
    p <- length(c(x, mbx))
    
    # learning local graph based on pc
    # only learn the skel and orient v-structures
    skel <- pcalg::skeleton(suffStat, indepTest, alpha, as.character(c(x, mbx)), method = 'original') 
    numtests <- numtests + sum(skel@n.edgetests)
    lx <- udag2pdagRelaxed(skel, orientCollider = TRUE, rules = rep(FALSE, 3))
    localMat <- as(lx@graph, 'matrix')
    subG <- matrix(0, p, p)
    for (i in 2:p){
      if (localMat[i, 1] == 1 & localMat[1, i] == 1){
        subG[i, 1] <- subG[1, i] <- 1
      }else if (localMat[i, 1] == 1 & localMat[1, i] == 0){
        subG[i, 1] <- 1
        subG[1, i] <- 0
      }else if (localMat[i, 1] == 0 & localMat[1, i] == 1){
        subG[i, 1] <- 1
        subG[1, i] <- 1
        # # for every node pointed at i but not adjacent to 1
        # cop <- which(localMat[, i] == 1 & localMat[i, ] == 0 
        #              & localMat[1, ] == 0 & localMat[, 1] == 0)
        # for (j in cop){
        #   subG[j, i] <- 1
        #   subG[i, j] <- 0
        # }
      }
    }
    
    # when a conflict ocurrs
    # a former directed edge will not be changed 
    # a former undiredcted will be changed as a new directed edge
    # the indept relations appear in marginal P are also appear in joint P
    # transform local sepsets into global ones
    subNames <- as.numeric(c(x, mbx))
    for (i in 1:(p-1)){
      for (j in (i+1):p){
        
        if (subG[i, j] == 1 & subG[j, i] == 1){
          if (G[subNames[i], subNames[j]] == 0 & G[subNames[j], subNames[i]] == 0) 
            G[subNames[i], subNames[j]] <- G[subNames[j], subNames[i]] <- 1
        }else if (subG[i, j] == 1 & subG[j, i] == 0){
          if (!(G[subNames[i], subNames[j]] == 0 & G[subNames[j], subNames[i]] == 1)){
            G[subNames[i], subNames[j]] <- 1
            G[subNames[j], subNames[i]] <- 0
          }
        }else if (subG[i, j] == 0 & subG[j, i] == 1){
          if (!(G[subNames[i], subNames[j]] == 1 & G[subNames[j], subNames[i]] == 0)){
            G[subNames[i], subNames[j]] <- 0
            G[subNames[j], subNames[i]] <- 1
          }
        }else{
          sepset[[subNames[i]]][[subNames[j]]] <- sepset[[subNames[j]]][[subNames[i]]] <- subNames[skel@sepset[[i]][[j]]]
        }
        
      }
    }
    
    G <- orientation(G, sepset)
    # colnames(G) <- varNames
    # rownames(G) <- varNames
    
    waitList <- rmvNodes(t, waitList, G)
    
  }
  res <- as(G, 'graphNEL')
  return(list(res, numtests))
}

# IAMB forward stage
iamb.forward<-function(x,p,suffStat,alpha, indepTest){
  
  # initialization
  ntests <- 0
  n <- p
  totalSet <- c(1: n)   
  set<-setdiff(totalSet, x)   
  cpc<-numeric()      
  leng=length(set)
  theta<-numeric(leng)
  
  
  for(i in 1:leng){
    m <- set[i]
    theta[i] <- indepTest(x,m,c(),suffStat)
    ntests <- ntests + 1
  }
  beta <- min(theta)
  select <-  set[which(theta[] == beta)[1]]
  
  # forward
  while(beta < alpha){ 
    cpc <- c(cpc, select)
    candidate <- setdiff(set,cpc)
    leng <- length(candidate)
    theta<-numeric(leng)
    if(leng != 0){
      for(i in 1:leng){
        m <- candidate[i]
        theta[i] <- indepTest(x,m,cpc,suffStat)
        ntests <- ntests + 1
      }
    }
    beta <- min(theta) 
    select <- candidate[which(theta[]==beta)[1]]
  }
  return(list(cpc, ntests))
}

# IAMB algorithm 
IAMB <- function(X, p, suffStat, alpha, indepTest){
  R <- iamb.forward(X,p,suffStat,alpha,indepTest)
  CPC <- R[[1]]
  ntests <- R[[2]]
  condition <- CPC
  if (length(condition) == 0){
    CPC <- c()
  }else{
    for (i in 1:length(condition)){
      tmp_cpc <- setdiff(CPC,condition[i])
      ntests <- ntests + 1
      if (indepTest(X, condition[i], tmp_cpc, suffStat) > alpha){
        CPC <- tmp_cpc
      }
    }
  }
  if (length(CPC) == 0){
    mat <- matrix(rep(-1, p), p, length(-1), byrow=TRUE)
    sepset.x <- split(mat, row(mat))
  }else{
    mat <- matrix(rep(CPC, p), p, length(CPC), byrow=TRUE)
    sepset.x <- split(mat, row(mat))
    sepset.x[[X]] <- -1
    sepset.x[CPC] <- -1
  }
  
  return(list(CPC, ntests))
}

weightAndSort <- function(gR, lb=0.1, ub=1){
  # sort the graph topologically and randomly weight the edges
  nodeList <- gR@nodes
  edg <- edgeMatrix(gR)
  ord <- tsort(gR)
  newNode <- numeric(length(ord))
  newEdge <- list()
  for (i in 1:length(ord)){
    newEdge[[i]] <- as.character(c())
    newNode[i] <- which(ord == i)
  }
  amat <- matrix(0, length(ord), length(ord))
  for (i in 1:ncol(edg)){
    amat[newNode[edg[1,i]], newNode[edg[2,i]]] <- 1
    newEdge[[newNode[edg[1,i]]]] <- c(newEdge[[newNode[edg[1,i]]]], newNode[edg[2,i]])
  }
  for (i in 1:length(ord)){
    newEdge[[i]] <- list(edges=newEdge[[i]], weights=runif(length(newEdge[[i]]),lb,ub))
  }
  names(newEdge) <- nodeList
  ngR <- graphNEL(nodeList, edgeL=newEdge, edgemode = 'directed')
}

weightNoSort <- function(gR, lb=0.1, ub=1){
  # randomly weight the edges
  nodeList <- dag@nodes
  edg <- edgeMatrix(gR)
  ord <- nodeList
  newNode <- numeric(length(ord))
  newEdge <- list()
  for (i in 1:length(ord)){
    newEdge[[i]] <- as.character(c())
    newNode[i] <- which(ord == i)
  }
  amat <- matrix(0, length(ord), length(ord))
  for (i in 1:ncol(edg)){
    amat[newNode[edg[1,i]], newNode[edg[2,i]]] <- 1
    newEdge[[newNode[edg[1,i]]]] <- c(newEdge[[newNode[edg[1,i]]]], newNode[edg[2,i]])
  }
  for (i in 1:length(ord)){
    newEdge[[i]] <- list(edges=newEdge[[i]], weights=runif(length(newEdge[[i]]),lb,ub))
  }
  names(newEdge) <- nodeList
  ngR <- graphNEL(nodeList, edgeL=newEdge, edgemode = 'directed')
}

causalTypeFromData <- function(f, t, data, indepTest = gaussCItest, alpha = 0.05, localDisc){
  # original local method demostrated in the paper submitted to IJCai
  undComp <- function(t, G){
    canV <- c(t)
    for (i in 1:nrow(G)){
      ind <- which(G[, canV] == 1 & t(G[canV, ]) == 1, arr.ind = TRUE)
      if (length(canV)==1){
        tmp <- unique(ind[, 2])
      }else{
        tmp <- unique(ind[, 1])
      }
      A <- union(canV, tmp)
      canV <- A
    }
    return(setdiff(canV, t))
  }
  
  ntests <- 0
  
  suffStat = list(C = cor(data), n = nrow(data))
  
  R1 <- localDisc(f, data, alpha, indepTest)
  rf <- R1[[1]]
  ntests <- ntests + R1[[2]]
  
  R2 <- localDisc(t, data, alpha, indepTest)
  rt <- R2[[1]]
  ntests <- ntests + R2[[2]]
  
  # rrf <- as.bn(rf)
  # rrt <- as.bn(rt)
  
  pa_f <- getNbr(rf, f)$parents
  ch_f <- getNbr(rf, f)$children
  sib_f <- getNbr(rf, f)$siblings
  
  pa_t <- getNbr(rt, t)$parents
  ch_t <- getNbr(rt, t)$children
  sib_t <- getNbr(rt, t)$siblings
  
  
  if (f %in% getNbr(rt, t)$nbr | t %in% getNbr(rf, f)$nbr){
    # 相邻判定
    # 矛盾判定无向,有向大于无向
    if ((f %in% pa_t & t %in% pa_f) | (f %in% ch_t & t %in% ch_f)){
      res <- c(1, 1)
    }else if (f %in% pa_t | t %in% ch_f){
      res <- c(2, 0)
    }else if (f %in% ch_t | t %in% pa_f){
      res <- c(0, 2)
    }else{
      res <- c(1, 1)
    }
  }else{
    # 检验判定
    t1 <- indepTest(f, t, pa_f, suffStat)
    t2 <- indepTest(f, t, pa_t, suffStat)
    ntests <- ntests + 2
    
    if (t1 > alpha & t2 > alpha){
      res <- c(0, 0)
    }else if (t1 <= alpha & t2 <= alpha){
      res <- c(1, 1)
    }else if (t1 <= alpha & t2 > alpha){
      # f is a potential cause of t
      t3 <- indepTest(f, t, c(pa_f, sib_f), suffStat)
      ntests <- ntests + 1
      if (t3 < alpha){
        res <- c(2, 0)
      }else{
        r <- divGraph(rf)
        ugMat <- as(r$ug, 'matrix')
        uc <- undComp(f, ugMat)
        z <- c()
        for (i in uc){
          R <- localDisc(i, data, alpha, indepTest)
          tmp <- R[[1]]
          ntests <- ntests + R[[2]]
          cond <- setdiff(getNbr(tmp,i)$nbr, getNbr(tmp,i)$children)
          if (i %in% pa_t | t %in% getNbr(tmp,i)$children){
            z <- c(z, i)
          }else{
            t4 <- indepTest(i, t, cond, suffStat)
            ntests <- ntests + 1
            if (t4 <= alpha){
              z <- c(z, i)
            }
          }
        }
        if (length(z) <= 1){
          res <- c(1, 0)
        }else{
          cs <- criticalSet(r$ug, f, z)
          ugm <- ugMat
          sub <- ugm[cs, cs]
          if (length(cs) == 0){
            res <- c(1, 0)
          }else if (sum(sub+diag(1,length(cs), length(cs)) != 1)==0){
            res <- c(1, 0)
          }else{
            res <- c(3, 0)
          }
        }
      }
    }else{
      # t is a potential cause of f
      t3 <- indepTest(f, t, c(pa_t, sib_t), suffStat)
      ntests <- ntests + 1
      if (t3 < alpha){
        res <- c(0, 2)
      }else{
        r <- divGraph(rt)
        ugMat <- as(r$ug, 'matrix')
        uc <- undComp(t, ugMat)
        z <- c()
        for (i in uc){
          R <- localDisc(i, data, alpha, indepTest)
          tmp <- R[[1]]
          ntests <- ntests + R[[2]]
          cond <- setdiff(getNbr(tmp,i)$nbr, getNbr(tmp,i)$children)
          if (i %in% pa_f | f %in% getNbr(tmp,i)$children){
            z <- c(z, i)
          }else{
            t4 <- indepTest(i, f, cond, suffStat)
            ntests <- ntests + 1
            if (t4 <= alpha){
              z <- c(z, i)
            }
          }
        }
        if (length(z) <= 1){
          res <- c(0, 1)
        }else{
          cs <- criticalSet(r$ug, t, z)
          ugm <- ugMat
          sub <- ugm[cs, cs]
          if (length(cs) == 0){
            res <- c(0, 1)
          }else if (sum(sub+diag(1,length(cs), length(cs)) != 1)==0){
            res <- c(0, 1)
          }else{
            res <- c(0, 3)
          }
        }
      }
    }
  }
  
  return(list(res=res, ntests=ntests))
}

causalTypeFromData_oracle <- function(f, t, tdag, indepTest = gaussCItest, alpha = 0.99999, localDisc){
  
  undComp <- function(t, G){
    canV <- c(t)
    for (i in 1:nrow(G)){
      ind <- which(G[, canV] == 1 & t(G[canV, ]) == 1, arr.ind = TRUE)
      if (length(canV)==1){
        tmp <- unique(ind[, 2])
      }else{
        tmp <- unique(ind[, 1])
      }
      A <- union(canV, tmp)
      canV <- A
    }
    return(setdiff(canV, t))
  }
  
  # CAUTION! the following step is neccesary!
  # dag <- weightAndSort(tdag, lb=0.1, ub=1)
  dag <- tdag
  cov.mat <- trueCov(dag)
  true.corr <- cov2cor(cov.mat)
  suffStat = list(C = true.corr, n = 10^9)
  
  rf <- localDisc(f, dag)
  rt <- localDisc(t, dag)
  
  rrf <- as.bn(rf)
  rrt <- as.bn(rt)
  
  pa_f <- rrf$nodes[[f]]$parents
  ch_f <- rrf$nodes[[f]]$children
  sib_f <- setdiff(setdiff(rrf$nodes[[f]]$nbr, pa_f), ch_f)
  
  pa_t <- rrt$nodes[[t]]$parents
  ch_t <- rrt$nodes[[t]]$children
  sib_t <- setdiff(setdiff(rrt$nodes[[t]]$nbr, pa_t), ch_t)
  
  
  if (f %in% rrt$nodes[[t]]$nbr | t %in% rrf$nodes[[f]]$nbr){
    # 相邻判定
    # 矛盾判定无向,有向大于无向
    if ((f %in% pa_t & t %in% pa_f) | (f %in% ch_t & t %in% ch_f)){
      res <- c(1, 1)
    }else if (f %in% pa_t | t %in% ch_f){
      res <- c(2, 0)
    }else if (f %in% ch_t | t %in% pa_f){
      res <- c(0, 2)
    }else{
      res <- c(1, 1)
    }
  }else{
    # 检验判定
    t1 <- indepTest(f, t, pa_f, suffStat)
    t2 <- indepTest(f, t, pa_t, suffStat)
    if (t1 > alpha & t2 > alpha){
      res <- c(0, 0)
    }else if (t1 <= alpha & t2 <= alpha){
      res <- c(1, 1)
    }else if (t1 <= alpha & t2 > alpha){
      # f is a potential cause of t
      t3 <- indepTest(f, t, c(pa_f, sib_f), suffStat)
      if (t3 < alpha){
        res <- c(2, 0)
      }else{
        r <- divGraph(rf)
        ugMat <- as(r$ug, 'matrix')
        uc <- undComp(f, ugMat)
        z <- c()
        for (i in uc){
          tmp <- as.bn(localDisc(i, dag))
          cond <- setdiff(tmp$nodes[[i]]$nbr, tmp$nodes[[i]]$children)
          if (i %in% pa_t | t %in% tmp$nodes[[i]]$children){
            z <- c(z, i)
          }else{
            t4 <- indepTest(i, t, cond, suffStat)
            if (t4 <= alpha){
              z <- c(z, i)
            }
          }
        }
        if (length(z) <= 1){
          res <- c(1, 0)
        }else{
          cs <- criticalSet(r$ug, f, z)
          ugm <- ugMat
          sub <- ugm[cs, cs]
          if (length(cs) == 0){
            res <- c(1, 0)
          }else if (sum(sub+diag(1,length(cs), length(cs)) != 1)==0){
            res <- c(1, 0)
          }else{
            res <- c(3, 0)
          }
        }
      }
    }else{
      # t is a potential cause of f
      t3 <- indepTest(f, t, c(pa_t, sib_t), suffStat)
      if (t3 < alpha){
        res <- c(0, 2)
      }else{
        r <- divGraph(rt)
        ugMat <- as(r$ug, 'matrix')
        uc <- undComp(t, ugMat)
        z <- c()
        for (i in uc){
          tmp <- as.bn(localDisc(i, dag))
          cond <- setdiff(tmp$nodes[[i]]$nbr, tmp$nodes[[i]]$children)
          if (i %in% pa_f | f %in% tmp$nodes[[i]]$children){
            z <- c(z, i)
          }else{
            t4 <- indepTest(i, f, cond, suffStat)
            if (t4 <= alpha){
              z <- c(z, i)
            }
          }
        }
        if (length(z) <= 1){
          res <- c(0, 1)
        }else{
          cs <- criticalSet(r$ug, t, z)
          ugm <- ugMat
          sub <- ugm[cs, cs]
          if (length(cs) == 0){
            res <- c(0, 1)
          }else if (sum(sub+diag(1,length(cs), length(cs)) != 1)==0){
            res <- c(0, 1)
          }else{
            res <- c(0, 3)
          }
        }
      }
    }
  }
  
  return(res)
}

getNbr <- function(g, i){
  # g is a graphNEL obj
  m <- as(g, 'matrix')
  pa <- which(m[, i] == 1 & m[i, ] == 0, arr.ind = TRUE)
  ch <- which(m[, i] == 0 & m[i, ] == 1, arr.ind = TRUE)
  sib <- which(m[, i] == 1 & m[i, ] == 1, arr.ind = TRUE)
  nbr <- which(m[, i] == 1 | m[i, ] == 1, arr.ind = TRUE)
  subg <- m[sort(sib), sort(sib)]
  # subg shouldn't contain any directed edge
  subg <- sign(subg+t(subg))
  if (length(subg)==1){
    subg <- as.matrix(subg, 1, 1)
  }
  colnames(subg) <- sort(sib)
  rownames(subg) <- sort(sib)
  gg <- as(subg, 'graphNEL')
  M <- maxClique(gg)$maxCliques
  return(list(parents = pa, children = ch, siblings = sib, nbr = nbr, mc = M))
  
}

causalTypeFromData_all <- function(data, indepTest = gaussCItest, alpha = 0.05, localDisc){
  # original local method demostrated in the paper submitted to IJCai
  undComp <- function(t, G){
    canV <- c(t)
    for (i in 1:nrow(G)){
      ind <- which(G[, canV] == 1 & t(G[canV, ]) == 1, arr.ind = TRUE)
      if (length(canV)==1){
        tmp <- unique(ind[, 2])
      }else{
        tmp <- unique(ind[, 1])
      }
      A <- union(canV, tmp)
      canV <- A
    }
    return(setdiff(canV, t))
  }
  
  suffStat = list(C = cor(data), n = nrow(data))
  
  ntests <- 0
  n <- ncol(data)
  lcmRes <- matrix(-1, n, n)
  
  for (f in 1:n){
    # cat('current node #',f, '\n')
    
    R1 <- localDisc(f, data, alpha, indepTest)
    rf <- R1[[1]]
    ntests <- ntests + R1[[2]]
    
    pa_f <- getNbr(rf, f)$parents
    ch_f <- getNbr(rf, f)$children
    sib_f <- getNbr(rf, f)$siblings
    
    for (t in 1:n){
      # print(t)
      if (t != f){
        if (t %in% pa_f){
          res <- 0
        }else if (t %in% ch_f){
          res <- 2
        }else if (t %in% sib_f){
          res <- 1
        }else{
          # 检验判定
          t1 <- indepTest(f, t, pa_f, suffStat)
          ntests <- ntests + 1
          
          if (t1 > alpha){
            res <- 0
          }else if (indepTest(f, t, c(pa_f, sib_f), suffStat)< alpha){
            ntests <- ntests + 1
            res <- 2
          }else{
            r <- divGraph(rf)
            ugMat <- as(r$ug, 'matrix')
            uc <- undComp(f, ugMat)
            z <- c()
            for (i in uc){
              R <- localDisc(i, data, alpha, indepTest)
              tmp <- R[[1]]
              ntests <- ntests + R[[2]]
              cond <- setdiff(getNbr(tmp,i)$nbr, getNbr(tmp,i)$children)
              if (t %in% getNbr(tmp,i)$children){
                z <- c(z, i)
              }else{
                t4 <- indepTest(i, t, cond, suffStat)
                ntests <- ntests + 1
                if (t4 <= alpha){
                  z <- c(z, i)
                }
              }
            }
            if (length(z) <= 1){
              res <- 1
            }else{
              cs <- criticalSet(r$ug, f, z)
              ugm <- ugMat
              sub <- ugm[cs, cs]
              if (length(cs) == 0){
                res <- 1
              }else if (sum(sub+diag(1,length(cs), length(cs)) != 1)==0){
                res <- 1
              }else{
                res <- 3
              }
            }
          }
        }
        lcmRes[f, t] <- res
      }else{
        lcmRes[f, t] <- -1
      }
    }
  }
  return(list(res=lcmRes, ntests=ntests/(n*(n-1))))
}

causalTypeFromData_all_oracle <- function(tdag, indepTest = gaussCItest, alpha = 0.999999, localDisc){
  # original local method demostrated in the paper submitted to IJCai
  undComp <- function(t, G){
    canV <- c(t)
    for (i in 1:nrow(G)){
      ind <- which(G[, canV] == 1 & t(G[canV, ]) == 1, arr.ind = TRUE)
      if (length(canV)==1){
        tmp <- unique(ind[, 2])
      }else{
        tmp <- unique(ind[, 1])
      }
      A <- union(canV, tmp)
      canV <- A
    }
    return(setdiff(canV, t))
  }
  
  dag <- tdag
  cov.mat <- trueCov(dag)
  true.corr <- cov2cor(cov.mat)
  suffStat = list(C = true.corr, n = 10^9)

  
  ntests <- 0
  n <- length(dag@nodes)
  lcmRes <- matrix(-1, n, n)
  
  for (f in 1:n){
    cat('current node #',f, '\n')
    
    rf <- localDisc(f, dag)
    rrf <- as.bn(rf)
    ntests <- ntests
    
    pa_f <- getNbr(rf, f)$parents
    ch_f <- getNbr(rf, f)$children
    sib_f <- getNbr(rf, f)$siblings
    
    for (t in 1:n){
      if (t != f){
        if (t %in% pa_f){
          res <- 0
        }else if (t %in% ch_f){
          res <- 2
        }else if (t %in% sib_f){
          res <- 1
        }else{
          # 检验判定
          t1 <- indepTest(f, t, pa_f, suffStat)
          ntests <- ntests + 1
          
          if (t1 > alpha){
            res <- 0
          }else if (indepTest(f, t, c(pa_f, sib_f), suffStat)< alpha){
            ntests <- ntests + 1
            res <- 2
          }else{
            r <- divGraph(rf)
            ugMat <- as(r$ug, 'matrix')
            uc <- undComp(f, ugMat)
            z <- c()
            for (i in uc){
              R <- localDisc(i,dag)
              tmp <- R
              ntests <- ntests
              cond <- setdiff(getNbr(tmp,i)$nbr, getNbr(tmp,i)$children)
              if (t %in% getNbr(tmp,i)$children){
                z <- c(z, i)
              }else{
                t4 <- indepTest(i, t, cond, suffStat)
                ntests <- ntests + 1
                if (t4 <= alpha){
                  z <- c(z, i)
                }
              }
            }
            if (length(z) <= 1){
              res <- 1
            }else{
              cs <- criticalSet(r$ug, f, z)
              ugm <- ugMat
              sub <- ugm[cs, cs]
              if (length(cs) == 0){
                res <- 1
              }else if (sum(sub+diag(1,length(cs), length(cs)) != 1)==0){
                res <- 1
              }else{
                res <- 3
              }
            }
          }
        }
        lcmRes[f, t] <- res
      }else{
        lcmRes[f, t] <- -1
      }
    }
  }
  return(list(res=lcmRes))
}

idaBased <- function(cov, g, p, alpha = 0.05, thr){
  tmp <- causalType(g)
  res = matrix(-1, p, p)
  for (i in 1:p){
    for (j in 1:p){
      if (i != j){
        suppressMessages(r <- ida(i, j, cov , g, method = "local",
            y.notparent = TRUE, type = "cpdag"))
        if (max(abs(r)) < thr){
          res[i, j] = 0
        }else if (min(abs(r)) < thr){
          res[i, j] = 1
        }else if (min(abs(r)) > thr){
          res[i, j] = tmp[i, j]
        }
      }
    }
  }
  return(res)
}

idaBased2 <- function(data, g, p, alpha = 0.05, thr = 0){
  tmp <- causalType(g)
  res = matrix(-1, p, p)
  for (i in 1:p){
    for (j in 1:p){
      if (i != j){
        suppressMessages(r <- myIda(i, j, data , g, alpha))
        if (max(abs(r)) < thr){
          res[i, j] = 0
        }else if (min(abs(r)) < thr){
          res[i, j] = 1
        }else if (min(abs(r)) > thr){
          res[i, j] = tmp[i, j]
        }
      }
    }
  }
  return(res)
}

idaAll <- function(cov, g, p, alpha = 0.05){
  tmp <- causalType(g)
  res = c()
  for (i in 1:p){
    for (j in 1:p){
      if (i != j){
        suppressMessages(r <- ida(i, j, cov , g, method = "local",
                                  y.notparent = TRUE, type = "cpdag"))
        res = c(res, r)
      }
    }
  }
  return(res)
}

idaAll2 <- function(cov, g, p, alpha = 0.05){
  tmp <- causalType(g)
  res = c()
  for (i in 1:p){
    for (j in 1:p){
      if (i != j){
        suppressMessages(r <- myIda(i, j, data , g, alpha))
        res = c(res, r)
      }
    }
  }
  return(res)
}

myIda <- function (x.pos, y.pos, data, graphEst, alpha, y.notparent = TRUE, verbose = FALSE, all.dags = NA) {
  
  stopifnot(x.pos == (x <- as.integer(x.pos)), y.pos == (y <- as.integer(y.pos)), 
            length(x) == 1, length(y) == 1)
  
  mcov = cov(data)
  method <- 'local'
  type <- "cpdag"
  amat <- ad.g <- wgtMatrix(graphEst)
  amat[which(amat != 0)] <- 1

  nl <- colnames(amat)
  stopifnot(!is.null(nl))
  amatSkel <- amat + t(amat)
  amatSkel[amatSkel != 0] <- 1
  if (method == "local") {
    wgt.est <- (ad.g != 0)
    if (y.notparent) {
      wgt.est[x, y] <- FALSE
    }
    tmp <- wgt.est - t(wgt.est)
    tmp[which(tmp < 0)] <- 0
    wgt.unique <- tmp
    pa1 <- which(wgt.unique[x, ] != 0)
    if (y %in% pa1) {
      beta.hat <- 0
    }
    else {
      wgt.ambig <- wgt.est - wgt.unique
      pa2 <- which(wgt.ambig[x, ] != 0)
      if (verbose) 
        cat("\n\nx=", x, "y=", y, "\npa1=", pa1, "\npa2=", 
            pa2, "\n")
      if (length(pa2) == 0) {
        beta.hat <- mylm(data, y, c(x, pa1), alpha)
        if (verbose) 
          cat("Fit - y:", y, "x:", c(x, pa1), "|b.hat=", 
              beta.hat, "\n")
      }
      else {
        beta.hat <- NA
        ii <- 0
        pa2.f <- pa2
        pa2.t <- NULL
        if (hasExtension(amat, amatSkel, x, pa1, pa2.t, 
                         pa2.f, type, nl)) {
          ii <- ii + 1
          beta.hat[ii] <- mylm(data, y, c(x, pa1), alpha)
          if (verbose) 
            cat("Fit - y:", y, "x:", c(x, pa1), "|b.hat=", 
                beta.hat[ii], "\n")
        }
        for (i2 in seq_along(pa2)) {
          pa2.f <- pa2[-i2]
          pa2.t <- pa2[i2]
          if (hasExtension(amat, amatSkel, x, pa1, pa2.t, 
                           pa2.f, type, nl)) {
            ii <- ii + 1
            if (y %in% pa2.t) {
              beta.hat[ii] <- 0
            }
            else {
              beta.hat[ii] <- mylm(data, y, c(x, pa1, 
                                                pa2[i2]), alpha)
              if (verbose) 
                cat("Fit - y:", y, "x:", c(x, pa1, pa2[i2]), 
                    "|b.hat=", beta.hat[ii], "\n")
            }
          }
        }
        if (length(pa2) > 1) 
          for (i in 2:length(pa2)) {
            pa.tmp <- combn(pa2, i, simplify = TRUE)
            for (j in seq_len(ncol(pa.tmp))) {
              pa2.t <- pa.tmp[, j]
              pa2.f <- setdiff(pa2, pa2.t)
              if (hasExtension(amat, amatSkel, x, pa1, 
                               pa2.t, pa2.f, type, nl)) {
                ii <- ii + 1
                if (y %in% pa2.t) {
                  beta.hat[ii] <- 0
                }
                else {
                  beta.hat[ii] <- mylm(data, y, c(x, 
                                                    pa1, pa2.t), alpha)
                  if (verbose) 
                    cat("Fit - y:", y, "x:", c(x, pa1, 
                                               pa2.t), "|b.hat=", beta.hat[ii], 
                        "\n")
                }
              }
            }
          }
      }
    }
  }
  unname(beta.hat)
}

mylm <- function(data, y, x, alpha){
  subdata <- data[,c(y,x)]
  colnames(subdata)[1] <- c('y')
  res <- lm(y ~ 0+., data = as.data.frame(subdata))
  r <- summary(res)
  pvalue <- r$coefficients[1,4]
  if (pvalue > alpha){
    return(0)
  }else{
    return(r$coefficients[1,1])
  }
}

hasExtension <- function(amat, amatSkel, x, pa1, pa2.t, pa2.f, type, nl) 
{
  if (type == "pdag") {
    xNL <- nl[x]
    fromXNL <- rep(xNL, length(pa2.f))
    toXNL <- rep(xNL, length(pa2.t))
    pa2.fNL <- nl[pa2.f]
    pa2.tNL <- nl[pa2.t]
    tmp <- addBgKnowledge(gInput = amat, x = c(fromXNL, 
                                               pa2.tNL), y = c(pa2.fNL, toXNL))
    res <- !is.null(tmp)
  }
  else {
    res <- !has.new.coll(amat, amatSkel, x, pa1, pa2.t, 
                         pa2.f)
  }
  res
}

has.new.coll <- function (amat, amatSkel, x, pa1, pa2.t, pa2.f) 
{
  res <- FALSE
  if (length(pa2.t) > 0 && !all(is.na(pa2.t))) {
    if (length(pa1) > 0 && !all(is.na(pa1))) {
      res <- min(amatSkel[pa1, pa2.t]) == 0
    }
    if (!res && length(pa2.t) > 1) {
      A2 <- amatSkel[pa2.t, pa2.t]
      diag(A2) <- 1
      res <- min(A2) == 0
    }
  }
  if (!res && length(pa2.f) > 0 && !all(is.na(pa2.f))) {
    A <- amat - t(amat)
    A[A < 0] <- 0
    cA <- colSums(A[pa2.f, , drop = FALSE])
    papa <- setdiff(which(cA != 0), x)
    if (length(papa) > 0) 
      res <- min(amatSkel[x, papa]) == 0
  }
  res
}








