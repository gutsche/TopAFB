#include <fstream>
#include "TH1D.h"
#include "TMatrixD.h"
#include "TMath.h"

double xsection = 154.0*0.06451;

int lineWidth=3;

TString observablename;
TString acceptanceName;
TString xaxislabel;
TString yaxislabel;
TString asymlabel;

float xmin1D=-1.0;
float xmax1D= 1.0;
float xmin=-1.0;
float xmax= 1.0;
float ymin=-1.0;
float ymax= 1.0;

const int nbins1D=6;
const int nbinsx2D=6; //Normal configuration: use 6 bins in x, before and after unfolding.
const int nbinsx2Dalt = 12; //Alternate configuration: use 12 bins in x before unfolding, and 6 bins after.
const int nbinsy2D=3;
const int nbinsunwrapped = nbinsx2D*nbinsy2D;
const int nbinsunwrappedalt = nbinsx2Dalt*nbinsy2D;

double xbins1D[nbins1D+1];
double xbins2D[nbinsx2D+1];
double xbins2Dalt[nbinsx2Dalt+1];
double ybins2D[nbinsy2D+1];


Double_t stat_corr  [nbins1D]; //errors include syst error in the unfolding
Double_t stat_uncorr[nbins1D]; //errors do not include syst error in the unfolding
Double_t syst_corr  [nbins1D];

Float_t sign(Float_t t) 
{
  if( t >= 0.0 )
    return 1.0;
  else
    return -1.0;
}


void GetAfb(TH1D* h, Float_t &afb, Float_t  &afberr){

  Int_t nbins = h->GetNbinsX();
  Float_t event_minus;
  Float_t event_plus;
  Float_t event_total;
  Double_t event_plus_err;
  Double_t event_minus_err;

  //event_minus  = h-> IntegralAndError(0, nbins/2, event_plus_err,"");
  event_minus  = h-> IntegralAndError(0, nbins/2, event_minus_err,"");
  //event_plus   = h-> IntegralAndError(nbins/2+1, nbins+1, event_minus_err,"");
  event_plus   = h-> IntegralAndError(nbins/2+1, nbins+1, event_plus_err,"");
  event_total = event_plus + event_minus;

  //cout<<event_minus<<" "<<event_minus_err<<" "<<event_plus<<" "<<event_plus_err<<" "<<event_total<<endl;

  afb = (event_plus-event_minus)/(event_plus+event_minus);
  afberr   = sqrt(4*(event_plus*event_plus*event_minus_err*event_minus_err 
    + event_minus*event_minus*event_plus_err*event_plus_err)/
    (event_total*event_total*event_total*event_total));

}

void GetAfb(TH2D* h, Float_t &afb, Float_t  &afberr){

  Int_t nbinsx = h->GetNbinsX();
  Int_t nbinsy = h->GetNbinsY();
  Float_t event_minus;
  Float_t event_plus;
  Float_t event_total;
  Double_t event_plus_err;
  Double_t event_minus_err;

  event_minus  = h->IntegralAndError(0, nbinsx/2, 0, nbinsy+1, event_minus_err,"");
  event_plus   = h->IntegralAndError(nbinsx/2+1, nbinsx+1, 0, nbinsy+1, event_plus_err,"");
  event_total = event_plus + event_minus;

  afb = (event_plus-event_minus)/(event_plus+event_minus);
  afberr   = sqrt(4*(event_plus*event_plus*event_minus_err*event_minus_err 
    + event_minus*event_minus*event_plus_err*event_plus_err)/
    (event_total*event_total*event_total*event_total));

}


void GetAfb_integratewidth(TH1D* h, Float_t &afb, Float_t  &afberr){

  Int_t nbins = h->GetNbinsX();
  Float_t event_minus;
  Float_t event_plus;
  Float_t event_total;
  Double_t event_plus_err;
  Double_t event_minus_err;

  event_minus  = h-> IntegralAndError(0, nbins/2, event_minus_err,"width");
  event_plus   = h-> IntegralAndError(nbins/2+1, nbins+1, event_plus_err,"width");
  event_total = event_plus + event_minus;

  afb = (event_plus-event_minus)/(event_plus+event_minus);
  afberr   = sqrt(4*(event_plus*event_plus*event_minus_err*event_minus_err 
    + event_minus*event_minus*event_plus_err*event_plus_err)/
    (event_total*event_total*event_total*event_total));

}


//void GetAfbBinByBin(TH1D* h, Float_t &afbbin, Float_t  &afberrbin){
void GetAfbBinByBin(TH1D* h){

  Int_t nbins = h->GetNbinsX();
  const int nbins2 = nbins/2 +1;
  Float_t event_minus[nbins2];
  Float_t event_plus[nbins2];
  Float_t event_total[nbins2];
  Double_t event_plus_err[nbins2];
  Double_t event_minus_err[nbins2];
  Double_t afbbin[nbins2];
  Double_t afberrbin[nbins2];

  Double_t event_plus_total = 0.;
  Double_t event_minus_total = 0.;
  Double_t event_total_total = 0.;

  for(int i=0;i<nbins2;i++){
    //event_minus[i]  = h-> IntegralAndError(i, i, event_plus_err[i],"");
    event_minus[i]  = h-> IntegralAndError(i, i, event_minus_err[i],"");
    event_minus_total += event_minus[i];
    //event_plus[i]   = h-> IntegralAndError(nbins+1-i, nbins+1-i, event_minus_err[i],"");
    event_plus[i]   = h-> IntegralAndError(nbins+1-i, nbins+1-i, event_plus_err[i],"");
    event_plus_total += event_plus[i];
    event_total[i] = event_plus[i] + event_minus[i];
    event_total_total += event_total[i];

    //cout<<event_minus[i]<<" "<<event_minus_err[i]<<" "<<event_plus[i]<<" "<<event_plus_err[i]<<" "<<event_total[i]<<endl;

    afbbin[i] = (event_plus[i]-event_minus[i])/(event_plus[i]+event_minus[i]);
    afberrbin[i]   = sqrt(4*(event_plus[i]*event_plus[i]*event_minus_err[i]*event_minus_err[i] 
      + event_minus[i]*event_minus[i]*event_plus_err[i]*event_plus_err[i])/
      (event_total[i]*event_total[i]*event_total[i]*event_total[i]));
    cout<<i<<" AFB = "<<afbbin[i]<<" +/- "<<afberrbin[i]<<endl;
  }
}


void GetAvsY(TH1* histogram, TMatrixD &covarianceM, vector<double> &myafb, vector<double> &myerr, ofstream& second_output_file){

  myafb.clear();
  myerr.clear();

    //Get info from histogram
  int nbins = histogram->GetNbinsX();
  double n[16];
  for(int i=0;i<nbins;i++){
    n[i] = histogram->GetBinContent(i+1);
  }

    //Output
  double afb[8], err[8];

    //Setup Some Needed Vectors
  double alpha[16], beta[16], dfdn[16];

    //Get Asymmetry for each Y bin
  for(int j=0;j<nbins/2;j++) {

    int forBin = nbins/2 + j;
    int bacBin = nbins/2 - j - 1;

    for(int i=0;i<nbins;i++){
      if( i == forBin ){ 
        alpha[i] = 1; 
        beta[i] = 1;
      }else if( i == bacBin ){ 
        alpha[i] = -1; 
        beta[i] = 1;
      }else{
        alpha[i] = 0;
        beta[i] = 0;
      }
    }

    double sum = 0. , diff = 0.;
    for(int i=0;i<nbins;i++){
      sum += beta[i] * n[i];
      diff += alpha[i] * n[i];
    }

      //Calculate Everything
    if(sum > 0){ 

  //Error Calculation
      for(int i=0;i<nbins;i++){
        dfdn[i] = ( alpha[i] * sum - beta[i] * diff ) / pow(sum,2);
      }

      double afberr = 0.;
      for(int i=0;i<nbins;i++){
        for(int k=0;k<nbins;k++){
          afberr += covarianceM(i,k) * dfdn[i] * dfdn[k];
      //if(i==k) cout<<"DAH: "<<n[i]<<" "<<k<<" "<<covarianceM(i,k)<<endl;
        }
      }
      afberr = sqrt(afberr);

      err[j] = afberr;
      afb[j] = diff / sum; 

    }else{ 

      afb[j] = 0.; 
      err[j] = 0.;

    }
    myafb.push_back(afb[j]);
    myerr.push_back(err[j]);

    cout<<j<<" AFB = "<<afb[j]<<" +/- "<<err[j]<<endl;
    second_output_file << acceptanceName << " " << observablename << " AFB" << j << ": " << afb[j] << " +/- " << err[j] << endl;    	
  }
}

void GetAvsY2d (TH2* h2, vector<double> &myafb, vector<double> &myerr, ofstream& second_output_file){

  myafb.clear();
  myerr.clear();

  Float_t rowafb;
  Float_t rowerr;

  int ny = h2->GetNbinsY();

  TH1D *rowhist;

  for(int i=1; i<=ny; i++) {

	rowhist = h2->ProjectionX("rowprojection", i, i, "");  // I verified that this works correctly even without option "e".

	GetAfb(rowhist, rowafb, rowerr);

	myafb.push_back(rowafb);
	myerr.push_back(rowerr);

	cout << i << " AFB = " << rowafb << " +/- " << rowerr << endl;
	second_output_file << acceptanceName << " " << observablename << " AFB" << i << ": " << rowafb << " +/- " << rowerr << endl;
  }

  delete rowhist;
}

void GetCorrectedAfb(TH1D* histogram, TMatrixD &covarianceM, Float_t &afb, Float_t  &afberr){

    //Need to calculate AFB and Error for the fully corrected distribution, m_correctE(j,i)

    //Get histogram info
  int nbins = histogram->GetNbinsX();
  double n[16];
  for(int i=0;i<nbins;i++){
    n[i] = histogram->GetBinContent(i+1);
  }

    //Setup Alpha Vector
  double alpha[16], beta[16];
  for(int i=0;i<nbins;i++) {
	if(i < nbins/2 ){ alpha[i] = -1;
	}
	else{ alpha[i] = 1;}
  }

    //Components of the error calculation
  double sum_n = 0.;
  double sum_alpha_n = 0.;
  for(int i=0;i<nbins;i++){
    sum_n += n[i];
    sum_alpha_n += alpha[i] * n[i];
  }

  double dfdn[16];
  for(int i=0;i<nbins;i++){
    dfdn[i] = ( alpha[i] * sum_n - sum_alpha_n ) / pow(sum_n,2);
  }

    //Error Calculation
  afberr = 0.;
  for(int i=0;i<nbins;i++){
    for(int j=0;j<nbins;j++){
      afberr += covarianceM(i,j) * dfdn[i] * dfdn[j];
    }
  }
  afberr = sqrt(afberr);

    //Calculate Afb
  afb = sum_alpha_n / sum_n;

    //    cout<<"AFB = "<<afb<<" "<<afberr<<endl;
}



void GetCorrectedAfb2d(TH2D* histogram, TMatrixD &covarianceM, vector<double> &myafb, vector<double> &myerr, ofstream& second_output_file){

    //calculate AFB, using covariance matrix, m_correctE(j,i), for the uncertainty

  myafb.clear();
  myerr.clear();

    //Get histogram info
  Int_t nbinsx = histogram->GetNbinsX();
  Int_t nbinsy = histogram->GetNbinsY();

  const Int_t numbinsx = nbinsx;
  const Int_t numbinsy = nbinsy;
  const Int_t numbinsxy = numbinsx*numbinsy;

  double afb[numbinsy+1] = {0.};
  double afberr[numbinsy+1] = {0.};

  double n[numbinsx][numbinsy];
  for(int i=0;i<numbinsx;i++){
    for(int j=0;j<numbinsy;j++){
      n[i][j] = histogram->GetBinContent(i+1,j+1);
    }
  }

    //Setup Alpha Vector
  double alpha[numbinsx], beta[numbinsx];
  for(int i=0;i<numbinsx;i++) if(i < numbinsx/2 ){ alpha[i] = -1;}else{ alpha[i] = 1;}

    //Components of the error calculation
  double sum_n[numbinsy] = {0.};
  double sum_alpha_n[numbinsy] = {0.};
  double sum_n_Inclusive = 0.;
  double sum_alpha_n_Inclusive = 0.;
  for(int i=0;i<numbinsx;i++){
    for(int j=0;j<numbinsy;j++){
      sum_n[j] += n[i][j];
      sum_alpha_n[j] += alpha[i] * n[i][j];
      sum_n_Inclusive += n[i][j];
      sum_alpha_n_Inclusive += alpha[i] * n[i][j];
    }
  }
    //AFB = SUM( n[i][j]*alpha[i] ) / SUM( n[i][j] )
    //dAFB/dn_ij = [ SUM( n[i][j] ) * alpha[i] -  SUM( n[i][j]*alpha[i] ) * ( 1 ) ]  / SUM( n[i][j] )^2
  double dfdn[numbinsx][numbinsy];
  double dfdnInclusive[numbinsx][numbinsy];
  for(int i=0;i<numbinsx;i++){
    for(int j=0;j<numbinsy;j++){
      dfdn[i][j] = ( alpha[i] * sum_n[j] - sum_alpha_n[j] ) / pow(sum_n[j],2);
      dfdnInclusive[i][j] = ( alpha[i] * sum_n_Inclusive - sum_alpha_n_Inclusive ) / pow(sum_n_Inclusive,2);
    }
  }

    //Error Calculation
  for(int i=0;i<numbinsxy;i++){
    for(int j=0;j<numbinsxy;j++){
      int i_2di = i % numbinsx;
      int i_2dj = i / numbinsx;
      int j_2di = j % numbinsx;
      int j_2dj = j / numbinsx;
      //cout<<"i: "<<i<<" "<<i_2di<<" "<<i_2dj<<" j: "<<j<<" "<<j_2di<<" "<<j_2dj<<endl;
      afberr[0] += covarianceM(i,j) * dfdnInclusive[i_2di][i_2dj] * dfdnInclusive[j_2di][j_2dj];
      if(i_2dj==j_2dj) afberr[i_2dj+1] += covarianceM(i,j) * dfdn[i_2di][i_2dj] * dfdn[j_2di][j_2dj]; 
    }
  }

    //Calculate Afb

  afb[0] = sum_alpha_n_Inclusive / sum_n_Inclusive;

  for (int j = 0; j < numbinsy+1; ++j)
  {
    afberr[j] = sqrt(afberr[j]);
    if(j>0) afb[j] = sum_alpha_n[j-1] / sum_n[j-1];
    myafb.push_back(afb[j]);
    myerr.push_back(afberr[j]);

    cout<<j<<" AFB = "<<afb[j]<<" +/- "<<afberr[j]<<endl;
    second_output_file << acceptanceName << " " << observablename << " AFB" << j << ": " << afb[j] << " +/- " << afberr[j] << endl; 

  }

}





void GetCorrectedAfb_integratewidth(TH1D* histogram, TMatrixD &covarianceM, Float_t &afb, Float_t  &afberr){

    //Need to calculate AFB and Error for the fully corrected distribution, m_correctE(j,i)

    //Get histogram info
  int nbins = histogram->GetNbinsX();
  double n[16];
  for(int i=0;i<nbins;i++){
    n[i] = histogram->GetBinContent(i+1) * histogram->GetBinWidth(i+1);
  }

    //Setup Alpha Vector
  double alpha[16], beta[16];
  for(int i=0;i<nbins;i++) if(i < nbins/2 ){ alpha[i] = -1;}else{ alpha[i] = 1;}

    //Components of the error calculation
  double sum_n = 0.;
  double sum_alpha_n = 0.;
  for(int i=0;i<nbins;i++){
    sum_n += n[i];
    sum_alpha_n += alpha[i] * n[i];
  }

  double dfdn[16];
  for(int i=0;i<nbins;i++){
    dfdn[i] = ( alpha[i] * sum_n - sum_alpha_n ) / pow(sum_n,2);
  }

    //Error Calculation
  afberr = 0.;
  for(int i=0;i<nbins;i++){
    for(int j=0;j<nbins;j++){
      afberr += covarianceM(i,j) * dfdn[i] * dfdn[j];
    }
  }
  afberr = sqrt(afberr);

    //Calculate Afb
  afb = sum_alpha_n / sum_n;

    //    cout<<"AFB = "<<afb<<" "<<afberr<<endl;
}


void GetCorrectedAfb_integratewidth_V(TH1D* histogram, TMatrixD &covarianceM, Float_t &afb, Float_t  &afberr){

    //Need to calculate AFB and Error for the fully corrected distribution, m_correctE(j,i)

    //Get histogram info
  int nbins = histogram->GetNbinsX();
  double n[16];
  for(int i=0;i<nbins;i++){
    n[i] = histogram->GetBinContent(i+1) * histogram->GetBinWidth(i+1);
  }

    //Setup Alpha Vector
  double alpha[16], beta[16];
  for(int i=0;i<nbins;i++) if(i < nbins/2 ){ alpha[i] = -1;}else{ alpha[i] = 1;}

    //Components of the error calculation
  double sum_n = 0.;
  double sum_alpha_n = 0.;
  for(int i=0;i<nbins;i++){
    sum_n += n[i];
    sum_alpha_n += alpha[i] * n[i];
  }

  double dfdn[16];
  for(int i=0;i<nbins;i++){
    dfdn[i] = ( alpha[i] * sum_n - sum_alpha_n ) / pow(sum_n,2);
  }

    //Error Calculation
  afberr = 0.;
  for(int i=0;i<nbins;i++){
    for(int j=0;j<nbins;j++){
      afberr += covarianceM(i,j) * dfdn[i] * dfdn[j] * histogram->GetBinWidth(i+1) * histogram->GetBinWidth(j+1);
    }
  }
  afberr = sqrt(afberr);

    //Calculate Afb
  afb = sum_alpha_n / sum_n;

    //    cout<<"AFB = "<<afb<<" "<<afberr<<endl;
}


void GetCorrectedAfbBinByBin(TH1D* histogram, TMatrixD &covarianceM, vector<double> &myafb, vector<double> &myerr, ofstream& second_output_file){

    //Need to calculate AFB and Error for the fully corrected distribution, m_correctE(j,i)

  myafb.clear();
  myerr.clear();

    //Get histogram info
  int nbins = histogram->GetNbinsX();
  const int nbins2 = nbins/2;

  Double_t afbbin[nbins2];
  Double_t afberrbin[nbins2];

  double n[16];
  for(int i=0;i<nbins;i++){
    n[i] = histogram->GetBinContent(i+1);
  }

    //Setup Alpha Vector
  double alpha[16], beta[16];
  for(int i=0;i<nbins;i++) if(i < nbins/2 ){ alpha[i] = -1;}else{ alpha[i] = 1;}

    //Components of the error calculation
  double sum_n[nbins2];
  double sum_alpha_n[nbins2];
  double sum_n_total = 0.;
  double sum_alpha_n_total = 0.;


  for(int i=0;i<nbins2;i++){
    sum_n[i] = n[i] + n[nbins-1-i];
    sum_alpha_n[i] = alpha[i] * n[i] + alpha[nbins-1-i] * n[nbins-1-i];
    sum_n_total += sum_n[i];
    sum_alpha_n_total += sum_alpha_n[i];
  }

  double dfdn[16];
  for(int i=0;i<nbins;i++){
    int k = -999;
    if (i < nbins2) k = i;
    else k = nbins-1-i;
    dfdn[i] = ( alpha[i] * sum_n[k] - sum_alpha_n[k] ) / pow(sum_n[k],2);
  }

    //Error Calculation

  for(int k=0;k<nbins2;k++){
    afberrbin[k] = 0.;
    for(int i=0;i<nbins;i++){
      for(int j=0;j<nbins;j++){
        if( (i==k || i==nbins-1-k ) && (j==k || j==nbins-1-k ) ) {
          afberrbin[k] += covarianceM(i,j) * dfdn[i] * dfdn[j];
              //cout<<covarianceM(i,j)<<" "<<dfdn[i]<<" "<<dfdn[j]<<" "<<endl;
        }
      }
    }
    afberrbin[k] = sqrt(afberrbin[k]);
    afbbin[k] = sum_alpha_n[k] / sum_n[k];
    cout<<k<<" AFB = "<<afbbin[k]<<" +/- "<<afberrbin[k]<<endl;
    second_output_file << acceptanceName << " " << observablename << " AFB" << i << ": " << afbbin[k] << " +/- " << afberrbin[k] << endl;

    myafb.push_back(afbbin[k]);
    myerr.push_back(afberrbin[k]);
  }
  double afb = sum_alpha_n_total / sum_n_total;
    //cout<<"AFB = "<<afb<<endl;
}







void Initialize1DBinning(int iVar){


  switch (iVar)
  {
    //   Lepton Charge Asymmetry
    case 0:
    {
      observablename="lep_charge_asymmetry";
      //xaxislabel="|#eta_{l+}|-|#eta_{l-}|";
      xaxislabel="#Delta|#eta_{l}|";
      acceptanceName="lepChargeAsym";
      asymlabel="A_{lepC}";
      xbins1D[0]=-2.0; xbins1D[1]=-0.8; xbins1D[2]=-0.4; xbins1D[3]=0.0; xbins1D[4]=0.4; xbins1D[5]=0.8; xbins1D[6]=2.0;
      xbins2Dalt[0]=-2.0; xbins2Dalt[2]=-0.8; xbins2Dalt[4]=-0.4; xbins2Dalt[6]=0.0; xbins2Dalt[8]=0.4; xbins2Dalt[10]=0.8; xbins2Dalt[12]=2.0;
      xbins2Dalt[1]=-1.4; xbins2Dalt[3]=-0.6; xbins2Dalt[5]=-0.2; xbins2Dalt[7]=0.2; xbins2Dalt[9]=0.6; xbins2Dalt[11]=1.4;
syst_corr[0] =  0.002297  ; stat_corr[0] =  0.005120  ; stat_uncorr[0] =  0.003483  ;
syst_corr[1] =  0.002641  ; stat_corr[1] =  0.006879  ; stat_uncorr[1] =  0.004675  ;
syst_corr[2] =  0.004607  ; stat_corr[2] =  0.007338  ; stat_uncorr[2] =  0.005284  ;
syst_corr[3] =  0.004939  ; stat_corr[3] =  0.007344  ; stat_uncorr[3] =  0.005309  ;
syst_corr[4] =  0.003144  ; stat_corr[4] =  0.006623  ; stat_uncorr[4] =  0.004689  ;
syst_corr[5] =  0.002847  ; stat_corr[5] =  0.004806  ; stat_uncorr[5] =  0.003518  ;
      xmin1D=-2.0;
      xmax1D= 2.0;
      break;
    }
    //   Lepton Azimuthal Asymmetry 2
    case 1:
    {
      observablename="lep_azimuthal_asymmetry2";
      xaxislabel="#Delta#phi_{l+l-}";
      acceptanceName="lepAzimAsym2";
      asymlabel="A_{#Delta#phi}";
      Double_t pi = 3.141592653589793;
      xbins1D[0]=0.0; xbins1D[1]=4.*pi/20.; xbins1D[2]=7.*pi/20.; xbins1D[3]=10.*pi/20.; xbins1D[4]=13.*pi/20.; xbins1D[5]=16.*pi/20.; xbins1D[6]=pi;
      xbins2Dalt[0]=0.0; xbins2Dalt[2]=4.*pi/20.; xbins2Dalt[4]=7.*pi/20.; xbins2Dalt[6]=10.*pi/20.; xbins2Dalt[8]=13.*pi/20.; xbins2Dalt[10]=16.*pi/20.; xbins2Dalt[12]=pi;
      xbins2Dalt[1]=2.*pi/20.; xbins2Dalt[3]=5.5*pi/20.; xbins2Dalt[5]=8.5*pi/20.; xbins2Dalt[7]=11.5*pi/20.; xbins2Dalt[9]=14.5*pi/20.; xbins2Dalt[11]=18.*pi/20.;
syst_corr[0] =  0.006053  ; stat_corr[0] =  0.007795  ; stat_uncorr[0] =  0.005697  ;
syst_corr[1] =  0.005288  ; stat_corr[1] =  0.006603  ; stat_uncorr[1] =  0.004705  ;
syst_corr[2] =  0.006699  ; stat_corr[2] =  0.006543  ; stat_uncorr[2] =  0.004353  ;
syst_corr[3] =  0.006641  ; stat_corr[3] =  0.006642  ; stat_uncorr[3] =  0.004428  ;
syst_corr[4] =  0.005460  ; stat_corr[4] =  0.006648  ; stat_uncorr[4] =  0.004907  ;
syst_corr[5] =  0.006443  ; stat_corr[5] =  0.008155  ; stat_uncorr[5] =  0.006332  ;
      xmin1D=0.0;
      xmax1D=pi;
      break;
    }
    //   Top Polarization
    case 2:
    {
      observablename="lep_costheta_cms";
      xaxislabel="cos(#theta_{l+})";
      acceptanceName="lepPlusCosTheta";
      asymlabel="A_{P+}";
      xbins1D[0]=-1.0; xbins1D[1]=-0.6; xbins1D[2]=-0.3; xbins1D[3]=0.0; xbins1D[4]=0.3; xbins1D[5]=0.6; xbins1D[6]=1.0;
syst_corr[0] =  0.020616  ; stat_corr[0] =  0.024436  ; stat_uncorr[0] =  0.017748  ;
syst_corr[1] =  0.013600  ; stat_corr[1] =  0.016636  ; stat_uncorr[1] =  0.012111  ;
syst_corr[2] =  0.009425  ; stat_corr[2] =  0.018346  ; stat_uncorr[2] =  0.012860  ;
syst_corr[3] =  0.008491  ; stat_corr[3] =  0.016185  ; stat_uncorr[3] =  0.011730  ;
syst_corr[4] =  0.013484  ; stat_corr[4] =  0.014609  ; stat_uncorr[4] =  0.010715  ;
syst_corr[5] =  0.020242  ; stat_corr[5] =  0.024646  ; stat_uncorr[5] =  0.016832  ;
      xmin1D=-1.0;
      xmax1D= 1.0;
      break;
    }
    //   Top Polarization using negatively charged leptons
    case 3:
    {
      observablename="lepMinus_costheta_cms";
      xaxislabel="cos(#theta_{l-})";
      acceptanceName="lepMinusCosTheta";
      asymlabel="A_{P-}";
      xbins1D[0]=-1.0; xbins1D[1]=-0.6; xbins1D[2]=-0.3; xbins1D[3]=0.0; xbins1D[4]=0.3; xbins1D[5]=0.6; xbins1D[6]=1.0;
syst_corr[0] =  0.018580  ; stat_corr[0] =  0.024218  ; stat_uncorr[0] =  0.017780  ;
syst_corr[1] =  0.007818  ; stat_corr[1] =  0.015829  ; stat_uncorr[1] =  0.012130  ;
syst_corr[2] =  0.004938  ; stat_corr[2] =  0.017465  ; stat_uncorr[2] =  0.012852  ;
syst_corr[3] =  0.008199  ; stat_corr[3] =  0.015869  ; stat_uncorr[3] =  0.011715  ;
syst_corr[4] =  0.010044  ; stat_corr[4] =  0.013843  ; stat_uncorr[4] =  0.010866  ;
syst_corr[5] =  0.010887  ; stat_corr[5] =  0.021370  ; stat_uncorr[5] =  0.017103  ;
      xmin1D=-1.0;
      xmax1D= 1.0;
      break;
    }
    //   Top Polarization combining positively and negatively charged leptons
    case 4:
    {
      observablename="lep_costheta_cms";
      xaxislabel="cos(#theta_{l})";
      acceptanceName="lepCosTheta";
      asymlabel="A_{P}";
      xbins1D[0]=-1.0; xbins1D[1]=-0.6; xbins1D[2]=-0.3; xbins1D[3]=0.0; xbins1D[4]=0.3; xbins1D[5]=0.6; xbins1D[6]=1.0;
syst_corr[0] =  0.018822  ; stat_corr[0] =  0.016913  ; stat_uncorr[0] =  0.012560  ;
syst_corr[1] =  0.009816  ; stat_corr[1] =  0.012074  ; stat_uncorr[1] =  0.008569  ;
syst_corr[2] =  0.005198  ; stat_corr[2] =  0.012027  ; stat_uncorr[2] =  0.009090  ;
syst_corr[3] =  0.007258  ; stat_corr[3] =  0.010142  ; stat_uncorr[3] =  0.008288  ;
syst_corr[4] =  0.011297  ; stat_corr[4] =  0.010730  ; stat_uncorr[4] =  0.007630  ;
syst_corr[5] =  0.014313  ; stat_corr[5] =  0.017201  ; stat_uncorr[5] =  0.011998  ;
      xmin1D=-1.0;
      xmax1D= 1.0;
      break;
    }
    //   Top Spin Correlation
    case 5:
    {
      observablename="top_spin_correlation";
      xaxislabel="cos(#theta_{l+})cos(#theta_{l-})";
      acceptanceName="topSpinCorr";
      asymlabel="A_{c1c2}";
      xbins1D[0]=-1.0; xbins1D[1]=-0.5; xbins1D[2]=-0.2; xbins1D[3]=0.0; xbins1D[4]=0.2; xbins1D[5]=0.5; xbins1D[6]=1.0;
syst_corr[0] =  0.010485  ; stat_corr[0] =  0.014863  ; stat_uncorr[0] =  0.010240  ;
syst_corr[1] =  0.022804  ; stat_corr[1] =  0.030016  ; stat_uncorr[1] =  0.020079  ;
syst_corr[2] =  0.033008  ; stat_corr[2] =  0.043863  ; stat_uncorr[2] =  0.031697  ;
syst_corr[3] =  0.030773  ; stat_corr[3] =  0.042290  ; stat_uncorr[3] =  0.028571  ;
syst_corr[4] =  0.023015  ; stat_corr[4] =  0.028738  ; stat_uncorr[4] =  0.019560  ;
syst_corr[5] =  0.008816  ; stat_corr[5] =  0.011391  ; stat_uncorr[5] =  0.007670  ;
      xmin1D=-1.0;
      xmax1D= 1.0;
      break;
    }
    //   Top Asy III
    case 6:
    {
      observablename="top_rapidtiydiff_Marco";
      //xaxislabel="|y_{top}|-|y_{tbar}|";
      xaxislabel="#Delta|y_{t}|";
      acceptanceName="rapiditydiffMarco";
      asymlabel="A_{C}";
      xbins1D[0]=-2.0; xbins1D[1]=-0.7; xbins1D[2]=-0.3; xbins1D[3]=0.0; xbins1D[4]=0.3; xbins1D[5]=0.7; xbins1D[6]=2.0;
syst_corr[0] =  0.004009  ; stat_corr[0] =  0.006765  ; stat_uncorr[0] =  0.004693  ;
syst_corr[1] =  0.005596  ; stat_corr[1] =  0.011998  ; stat_uncorr[1] =  0.008558  ;
syst_corr[2] =  0.007438  ; stat_corr[2] =  0.014062  ; stat_uncorr[2] =  0.010686  ;
syst_corr[3] =  0.010550  ; stat_corr[3] =  0.014289  ; stat_uncorr[3] =  0.010699  ;
syst_corr[4] =  0.005315  ; stat_corr[4] =  0.011317  ; stat_uncorr[4] =  0.008462  ;
syst_corr[5] =  0.002776  ; stat_corr[5] =  0.006236  ; stat_uncorr[5] =  0.004700  ;
      xmin1D=-2.0;
      xmax1D= 2.0;
      break;
    }
    //   Top Charge Asymmetry
    case 7:
    {
      observablename="top_costheta_cms";
      xaxislabel="cos(#theta_{top})";
      acceptanceName="topCosTheta";
      asymlabel="A_{FB}";
      xbins1D[0]=-1.0; xbins1D[1]=-0.7; xbins1D[2]=-0.4; xbins1D[3]=0.0; xbins1D[4]=0.4; xbins1D[5]=0.7; xbins1D[6]=1.0;
syst_corr[0] =  0.018683  ; stat_corr[0] =  0.033209  ; stat_uncorr[0] =  0.024855  ;
syst_corr[1] =  0.009716  ; stat_corr[1] =  0.013867  ; stat_uncorr[1] =  0.010505  ;
syst_corr[2] =  0.006083  ; stat_corr[2] =  0.010515  ; stat_uncorr[2] =  0.008204  ;
syst_corr[3] =  0.004476  ; stat_corr[3] =  0.010134  ; stat_uncorr[3] =  0.008252  ;
syst_corr[4] =  0.008342  ; stat_corr[4] =  0.012908  ; stat_uncorr[4] =  0.010373  ;
syst_corr[5] =  0.016122  ; stat_corr[5] =  0.032788  ; stat_uncorr[5] =  0.024581  ;
      xmin1D=-1.0;
      xmax1D= 1.0;
      break;
    }
    //   Lepton Azimuthal Asymmetry
    case 8:
    {
      observablename="lep_azimuthal_asymmetry";
      xaxislabel="cos(#Delta#phi_{l+l-})";
      acceptanceName="lepAzimAsym";
      asymlabel="A_{#Delta#phi}";
      xbins1D[0]=-1.0; xbins1D[1]=-0.8; xbins1D[2]=-0.4; xbins1D[3]=0.0; xbins1D[4]=0.4; xbins1D[5]=0.8; xbins1D[6]=1.0;
      stat_corr[0] = 0.01; stat_corr [1] = 0.01;  stat_corr [2] = 0.01;  stat_corr [3] = 0.01; stat_corr [4] = 0.01;  stat_corr [5] = 0.01;  stat_corr [6] = 0.01; 
      stat_uncorr[0] = 0.00; stat_uncorr[1] = 0.00; stat_uncorr[2] = 0.00; stat_uncorr[3] = 0.00; stat_uncorr[4] = 0.00; stat_uncorr[5] = 0.00; stat_uncorr[6] = 0.00;
      syst_corr[0] = 0.02; syst_corr [1] = 0.02;  syst_corr [2] = 0.02;  syst_corr [3] = 0.02; syst_corr [4] = 0.02;  syst_corr [5] = 0.02;  syst_corr [6] = 0.02; 
      xmin1D=-1.0;
      xmax1D= 1.0;
      break;
    }
    //   Top Asy I
    case 9:
    {
      observablename="top_pseudorapidtiydiff_cms";
      xaxislabel="|#eta_{t}|-|#eta_{#bar{t}}|";
      acceptanceName="pseudorapiditydiff";
      asymlabel="A_{C}";
      xbins1D[0]=-2.0; xbins1D[1]=-1.0; xbins1D[2]=-0.5; xbins1D[3]=0.0; xbins1D[4]=0.5; xbins1D[5]=1.0; xbins1D[6]=2.0;
      stat_corr[0] = 0.01; stat_corr [1] = 0.01;  stat_corr [2] = 0.01;  stat_corr [3] = 0.01; stat_corr [4] = 0.01;  stat_corr [5] = 0.01;  stat_corr [6] = 0.01; 
      stat_uncorr[0] = 0.00; stat_uncorr[1] = 0.00; stat_uncorr[2] = 0.00; stat_uncorr[3] = 0.00; stat_uncorr[4] = 0.00; stat_uncorr[5] = 0.00; stat_uncorr[6] = 0.00;
      syst_corr[0] = 0.02; syst_corr [1] = 0.02;  syst_corr [2] = 0.02;  syst_corr [3] = 0.02; syst_corr [4] = 0.02;  syst_corr [5] = 0.02;  syst_corr [6] = 0.02; 
      xmin1D=-2.0;
      xmax1D= 2.0;
      break;
    }
    //   Top Asy II
    case 10:
    {
      observablename="top_rapidtiydiff_cms";
      xaxislabel="(y_{top}-y_{#bar{t}})(y_{top}+y_{#bar{t}})";
      acceptanceName="rapiditydiff";
      asymlabel="A_{C}";
      xbins1D[0]=-2.0; xbins1D[1]=-0.8; xbins1D[2]=-0.3; xbins1D[3]=0.0; xbins1D[4]=0.3; xbins1D[5]=0.8; xbins1D[6]=2.0;
      stat_corr[0] = 0.01; stat_corr [1] = 0.01;  stat_corr [2] = 0.01;  stat_corr [3] = 0.01; stat_corr [4] = 0.01;  stat_corr [5] = 0.01;  stat_corr [6] = 0.01; 
      stat_uncorr[0] = 0.00; stat_uncorr[1] = 0.00; stat_uncorr[2] = 0.00; stat_uncorr[3] = 0.00; stat_uncorr[4] = 0.00; stat_uncorr[5] = 0.00; stat_uncorr[6] = 0.00;
      syst_corr[0] = 0.02; syst_corr [1] = 0.02;  syst_corr [2] = 0.02;  syst_corr [3] = 0.02; syst_corr [4] = 0.02;  syst_corr [5] = 0.02;  syst_corr [6] = 0.02; 
      xmin1D=-2.0;
      xmax1D= 2.0;
      break;
    }
    default:
    {
      cout<<"Set the variable switch";
    }
  }
}

void Initialize2DBinning(int iVar){

  ybins2D[0]=0.0; ybins2D[1]=430; ybins2D[2]=530.0; ybins2D[3]=1200.0;  // KIT binning
  //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;   // SnT binning

  switch (iVar)
  {
    //   Lepton Charge Asymmetry
    case 0:
    {
      observablename="lep_charge_asymmetry";
      xaxislabel="#Delta|#eta_{l}|";
      yaxislabel="M_{t#bar t}";
      acceptanceName="lepChargeAsym";
      asymlabel="A_{lepC}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.8; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.8; xbins2D[6]=2.0;
      xbins2Dalt[0]=-2.0; xbins2Dalt[2]=-0.8; xbins2Dalt[4]=-0.4; xbins2Dalt[6]=0.0; xbins2Dalt[8]=0.4; xbins2Dalt[10]=0.8; xbins2Dalt[12]=2.0;
      xbins2Dalt[1]=-1.4; xbins2Dalt[3]=-0.6; xbins2Dalt[5]=-0.2; xbins2Dalt[7]=0.2; xbins2Dalt[9]=0.6; xbins2Dalt[11]=1.4;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2Dalt[0];
      xmax=xbins2Dalt[12];
syst_corr[0] =  0.016998  ; stat_corr[0] =  0.022320  ; stat_uncorr[0] =  0.017124  ;
syst_corr[1] =  0.006644  ; stat_corr[1] =  0.016393  ; stat_uncorr[1] =  0.011733  ;
syst_corr[2] =  0.008050  ; stat_corr[2] =  0.024319  ; stat_uncorr[2] =  0.016565  ;
      break;
    }
    //   Lepton Azimuthal Asymmetry 2
    case 1:
    {
      observablename="lep_azimuthal_asymmetry2";
      xaxislabel="#Delta#phi_{l+l-}";
      yaxislabel="M_{t#bar t}";
      acceptanceName="lepAzimAsym2";
      asymlabel="A_{#Delta#phi}";
      Double_t pi = 3.141592653589793;
      xbins2D[0]=0.0; xbins2D[1]=4.*pi/20.; xbins2D[2]=7.*pi/20.; xbins2D[3]=10.*pi/20.; xbins2D[4]=13.*pi/20.; xbins2D[5]=16.*pi/20.; xbins2D[6]=pi;
      xbins2Dalt[0]=0.0; xbins2Dalt[2]=4.*pi/20.; xbins2Dalt[4]=7.*pi/20.; xbins2Dalt[6]=10.*pi/20.; xbins2Dalt[8]=13.*pi/20.; xbins2Dalt[10]=16.*pi/20.; xbins2Dalt[12]=pi;
      xbins2Dalt[1]=2.*pi/20.; xbins2Dalt[3]=5.5*pi/20.; xbins2Dalt[5]=8.5*pi/20.; xbins2Dalt[7]=11.5*pi/20.; xbins2Dalt[9]=14.5*pi/20.; xbins2Dalt[11]=18.*pi/20.;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2Dalt[0];
      xmax=xbins2Dalt[12];
syst_corr[0] =  0.021257  ; stat_corr[0] =  0.024925  ; stat_uncorr[0] =  0.016828  ;
syst_corr[1] =  0.019863  ; stat_corr[1] =  0.018320  ; stat_uncorr[1] =  0.012061  ;
syst_corr[2] =  0.020331  ; stat_corr[2] =  0.022368  ; stat_uncorr[2] =  0.015599  ;
      break;
    }
    //   Top Polarization
    case 2:
    {
      observablename="lep_costheta_cms";
      xaxislabel="cos(#theta_{l+})";
      yaxislabel="M_{t#bar t}";
      acceptanceName="lepPlusCosTheta";
      asymlabel="A_{P+}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.029917  ; stat_corr[0] =  0.037317  ; stat_uncorr[0] =  0.026736  ;
syst_corr[1] =  0.033959  ; stat_corr[1] =  0.031844  ; stat_uncorr[1] =  0.022808  ;
syst_corr[2] =  0.042369  ; stat_corr[2] =  0.033700  ; stat_uncorr[2] =  0.023730  ;
      break;
    }
      //   Top Polarization using negatively charged leptons
    case 3:
    {
      observablename="lepMinus_costheta_cms";
      xaxislabel="cos(#theta_{l-})";
      yaxislabel="M_{t#bar t}";
      acceptanceName="lepMinusCosTheta";
      asymlabel="A_{P-}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.024935  ; stat_corr[0] =  0.036689  ; stat_uncorr[0] =  0.026769  ;
syst_corr[1] =  0.023687  ; stat_corr[1] =  0.031859  ; stat_uncorr[1] =  0.022936  ;
syst_corr[2] =  0.032852  ; stat_corr[2] =  0.033270  ; stat_uncorr[2] =  0.023972  ;
      break;
    }
      //   Top Polarization combining positively and negatively charged leptons
    case 4:
    {
      observablename="lep_costheta_cms";
      xaxislabel="cos(#theta_{l})";
      yaxislabel="M_{t#bar t}";
      acceptanceName="lepCosTheta";
      asymlabel="A_{P}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.024930  ; stat_corr[0] =  0.027112  ; stat_uncorr[0] =  0.018918  ;
syst_corr[1] =  0.026893  ; stat_corr[1] =  0.023475  ; stat_uncorr[1] =  0.016173  ;
syst_corr[2] =  0.036177  ; stat_corr[2] =  0.023908  ; stat_uncorr[2] =  0.016863  ;
      break;
    }
    //   Top Spin Correlation
    case 5:
    {
      observablename="top_spin_correlation";
      xaxislabel="cos(#theta_{l+})cos(#theta_{l-})";
      yaxislabel="M_{t#bar t}";
      acceptanceName="topSpinCorr";
      asymlabel="A_{c1c2}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.5; xbins2D[2]=-0.2; xbins2D[3]=0.0; xbins2D[4]=0.2; xbins2D[5]=0.5; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.048056  ; stat_corr[0] =  0.050683  ; stat_uncorr[0] =  0.035421  ;
syst_corr[1] =  0.039951  ; stat_corr[1] =  0.048078  ; stat_uncorr[1] =  0.033708  ;
syst_corr[2] =  0.034279  ; stat_corr[2] =  0.048239  ; stat_uncorr[2] =  0.034078  ;
      break;
    }
    //   Top Asy III
    case 6:
    {
      observablename="top_rapidtiydiff_Marco";
      //xaxislabel="|y_{top}|-|y_{tbar}|";
      xaxislabel="#Delta|y_{t}|";
      yaxislabel="M_{t#bar t}";
      acceptanceName="rapiditydiffMarco";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.7; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.7; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.011114  ; stat_corr[0] =  0.035540  ; stat_uncorr[0] =  0.026775  ;
syst_corr[1] =  0.008458  ; stat_corr[1] =  0.030802  ; stat_uncorr[1] =  0.023539  ;
syst_corr[2] =  0.009106  ; stat_corr[2] =  0.030456  ; stat_uncorr[2] =  0.023472  ;
      break;
    }
    //   Top Charge Asymmetry
    case 7:
    {
      observablename="top_costheta_cms";
      xaxislabel="cos(#theta_{top})";
      yaxislabel="M_{t#bar t}";
      acceptanceName="topCosTheta";
      asymlabel="A_{FB}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.7; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.7; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.009239  ; stat_corr[0] =  0.039108  ; stat_uncorr[0] =  0.027033  ;
syst_corr[1] =  0.008722  ; stat_corr[1] =  0.034257  ; stat_uncorr[1] =  0.023779  ;
syst_corr[2] =  0.009654  ; stat_corr[2] =  0.033674  ; stat_uncorr[2] =  0.023725  ;
      break;
    }
    //   Lepton Azimuthal Asymmetry
    case 8:
    {
      observablename="lep_azimuthal_asymmetry";
      xaxislabel="cos(#Delta#phi_{l+l-})";
      yaxislabel="M_{t#bar t}";
      acceptanceName="lepAzimAsym";
      asymlabel="A_{#Delta#phi}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.8; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.8; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    //   Top Asy I
    case 9:
    {
      observablename="top_pseudorapidtiydiff_cms";
      xaxislabel="|#eta_{t}|-|#eta_{#bar{t}}|";
      yaxislabel="M_{t#bar t}";
      acceptanceName="pseudorapiditydiff";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-1.0; xbins2D[2]=-0.5; xbins2D[3]=0.0; xbins2D[4]=0.5; xbins2D[5]=1.0; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    //   Top Asy II
    case 10:
    {
      observablename="top_rapidtiydiff_cms";
      xaxislabel="(y_{top}-y_{#bar{t}})(y_{top}+y_{#bar{t}})";
      yaxislabel="M_{t#bar t}";
      acceptanceName="rapiditydiff";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.8; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.8; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=410; ybins2D[2]=510.0; ybins2D[3]=800.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    default:
    {
      cout<<"Set the variable switch";
    }
  }
}

void Initialize2DBinningttpt(int iVar){

  ybins2D[0]=0.0; ybins2D[1]=41.0; ybins2D[2]=92.0; ybins2D[3]=300.0;  //KIT
  //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;  //SnT

  switch (iVar)
  {
    //   Lepton Charge Asymmetry
    case 0:
    {
      observablename="lep_charge_asymmetry";
      xaxislabel="#Delta|#eta_{l}|";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="lepChargeAsym";
      asymlabel="A_{lepC}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.8; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.8; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.008158  ; stat_corr[0] =  0.022313  ; stat_uncorr[0] =  0.015035  ;
syst_corr[1] =  0.005504  ; stat_corr[1] =  0.018329  ; stat_uncorr[1] =  0.011670  ;
syst_corr[2] =  0.007788  ; stat_corr[2] =  0.022922  ; stat_uncorr[2] =  0.015675  ;
      break;
    }
    //   Lepton Azimuthal Asymmetry 2
    case 1:
    {
      observablename="lep_azimuthal_asymmetry2";
      xaxislabel="#Delta#phi_{l+l-}";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="lepAzimAsym2";
      asymlabel="A_{#Delta#phi}";
      Double_t pi = 3.141592653589793;
      xbins2D[0]=0.0; xbins2D[1]=4.*pi/20.; xbins2D[2]=7.*pi/20.; xbins2D[3]=10.*pi/20.; xbins2D[4]=13.*pi/20.; xbins2D[5]=16.*pi/20.; xbins2D[6]=pi;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.014243  ; stat_corr[0] =  0.019780  ; stat_uncorr[0] =  0.014620  ;
syst_corr[1] =  0.012334  ; stat_corr[1] =  0.016535  ; stat_uncorr[1] =  0.011741  ;
syst_corr[2] =  0.021710  ; stat_corr[2] =  0.024488  ; stat_uncorr[2] =  0.015417  ;
      break;
    }
    //   Top Polarization
    case 2:
    {
      observablename="lep_costheta_cms";
      xaxislabel="cos(#theta_{l+})";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="lepPlusCosTheta";
      asymlabel="A_{P+}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.033745  ; stat_corr[0] =  0.030063  ; stat_uncorr[0] =  0.023594  ;
syst_corr[1] =  0.029720  ; stat_corr[1] =  0.029505  ; stat_uncorr[1] =  0.023105  ;
syst_corr[2] =  0.029761  ; stat_corr[2] =  0.033696  ; stat_uncorr[2] =  0.025730  ;
      break;
    }
      //   Top Polarization using negatively charged leptons
    case 3:
    {
      observablename="lepMinus_costheta_cms";
      xaxislabel="cos(#theta_{l-})";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="lepMinusCosTheta";
      asymlabel="A_{P-}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.022499  ; stat_corr[0] =  0.033224  ; stat_uncorr[0] =  0.023700  ;
syst_corr[1] =  0.021051  ; stat_corr[1] =  0.032523  ; stat_uncorr[1] =  0.023232  ;
syst_corr[2] =  0.025551  ; stat_corr[2] =  0.036391  ; stat_uncorr[2] =  0.025822  ;
      break;
    }
      //   Top Polarization combining positively and negatively charged leptons
    case 4:
    {
      observablename="lep_costheta_cms";
      xaxislabel="cos(#theta_{l})";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="lepCosTheta";
      asymlabel="A_{P}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.025287  ; stat_corr[0] =  0.023151  ; stat_uncorr[0] =  0.016723  ;
syst_corr[1] =  0.022376  ; stat_corr[1] =  0.022412  ; stat_uncorr[1] =  0.016383  ;
syst_corr[2] =  0.023435  ; stat_corr[2] =  0.024692  ; stat_uncorr[2] =  0.018227  ;
      break;
    }
    //   Top Spin Correlation
    case 5:
    {
      observablename="top_spin_correlation";
      xaxislabel="cos(#theta_{l+})cos(#theta_{l-})";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="topSpinCorr";
      asymlabel="A_{c1c2}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.5; xbins2D[2]=-0.2; xbins2D[3]=0.0; xbins2D[4]=0.2; xbins2D[5]=0.5; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.036642  ; stat_corr[0] =  0.045355  ; stat_uncorr[0] =  0.033694  ;
syst_corr[1] =  0.034405  ; stat_corr[1] =  0.045849  ; stat_uncorr[1] =  0.034462  ;
syst_corr[2] =  0.029763  ; stat_corr[2] =  0.048965  ; stat_uncorr[2] =  0.036869  ;
      break;
    }
    //   Top Asy III
    case 6:
    {
      observablename="top_rapidtiydiff_Marco";
      //xaxislabel="|y_{top}|-|y_{tbar}|";
      xaxislabel="#Delta|y_{t}|";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="rapiditydiffMarco";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.7; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.7; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.007377  ; stat_corr[0] =  0.030828  ; stat_uncorr[0] =  0.024441  ;
syst_corr[1] =  0.008522  ; stat_corr[1] =  0.031094  ; stat_uncorr[1] =  0.024113  ;
syst_corr[2] =  0.007963  ; stat_corr[2] =  0.035538  ; stat_uncorr[2] =  0.026647  ;
      break;
    }
    //   Top Charge Asymmetry
    case 7:
    {
      observablename="top_costheta_cms";
      xaxislabel="cos(#theta_{top})";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="topCosTheta";
      asymlabel="A_{FB}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.7; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.7; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.006510  ; stat_corr[0] =  0.033293  ; stat_uncorr[0] =  0.024629  ;
syst_corr[1] =  0.008875  ; stat_corr[1] =  0.033379  ; stat_uncorr[1] =  0.024297  ;
syst_corr[2] =  0.012402  ; stat_corr[2] =  0.037342  ; stat_uncorr[2] =  0.026845  ;
      break;
    }
    //   Lepton Azimuthal Asymmetry
    case 8:
    {
      observablename="lep_azimuthal_asymmetry";
      xaxislabel="cos(#Delta#phi_{l+l-})";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="lepAzimAsym";
      asymlabel="A_{#Delta#phi}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.8; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.8; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    //   Top Asy I
    case 9:
    {
      observablename="top_pseudorapidtiydiff_cms";
      xaxislabel="|#eta_{t}|-|#eta_{#bar{t}}|";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="pseudorapiditydiff";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-1.0; xbins2D[2]=-0.5; xbins2D[3]=0.0; xbins2D[4]=0.5; xbins2D[5]=1.0; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    //   Top Asy II
    case 10:
    {
      observablename="top_rapidtiydiff_cms";
      xaxislabel="(y_{top}-y_{#bar{t}})(y_{top}+y_{#bar{t}})";
      yaxislabel="p_{T,t#bar{t}}";
      acceptanceName="rapiditydiff";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.8; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.8; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=24; ybins2D[2]=52.0; ybins2D[3]=100.0;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    default:
    {
      cout<<"Set the variable switch";
    }
  }
}

void Initialize2DBinningttrapidity2(int iVar){

  ybins2D[0]=0.0; ybins2D[1]=0.34; ybins2D[2]=0.75; ybins2D[3]=1.5;  //KIT
  //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;  //SnT

  switch (iVar)
  {
    //   Lepton Charge Asymmetry
    case 0:
    {
      observablename="lep_charge_asymmetry";
      xaxislabel="#Delta|#eta_{l}|";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="lepChargeAsym";
      asymlabel="A_{lepC}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.8; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.8; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.015588  ; stat_corr[0] =  0.020977  ; stat_uncorr[0] =  0.015600  ;
syst_corr[1] =  0.005081  ; stat_corr[1] =  0.016176  ; stat_uncorr[1] =  0.011712  ;
syst_corr[2] =  0.016189  ; stat_corr[2] =  0.020275  ; stat_uncorr[2] =  0.015549  ;
      break;
    }
    //   Lepton Azimuthal Asymmetry 2
    case 1:
    {
      observablename="lep_azimuthal_asymmetry2";
      xaxislabel="#Delta#phi_{l+l-}";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="lepAzimAsym2";
      asymlabel="A_{#Delta#phi}";
      Double_t pi = 3.141592653589793;
      xbins2D[0]=0.0; xbins2D[1]=4.*pi/20.; xbins2D[2]=7.*pi/20.; xbins2D[3]=10.*pi/20.; xbins2D[4]=13.*pi/20.; xbins2D[5]=16.*pi/20.; xbins2D[6]=pi;
      ybins2D=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.013842  ; stat_corr[0] =  0.020087  ; stat_uncorr[0] =  0.014961  ;
syst_corr[1] =  0.013551  ; stat_corr[1] =  0.015213  ; stat_uncorr[1] =  0.011771  ;
syst_corr[2] =  0.019025  ; stat_corr[2] =  0.019016  ; stat_uncorr[2] =  0.015017  ;
      break;
    }
    //   Top Polarization
    case 2:
    {
      observablename="lep_costheta_cms";
      xaxislabel="cos(#theta_{l+})";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="lepPlusCosTheta";
      asymlabel="A_{P+}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.035835  ; stat_corr[0] =  0.033497  ; stat_uncorr[0] =  0.024119  ;
syst_corr[1] =  0.030587  ; stat_corr[1] =  0.031589  ; stat_uncorr[1] =  0.023099  ;
syst_corr[2] =  0.032040  ; stat_corr[2] =  0.033993  ; stat_uncorr[2] =  0.025467  ;
      break;
    }
      //   Top Polarization using negatively charged leptons
    case 3:
    {
      observablename="lepMinus_costheta_cms";
      xaxislabel="cos(#theta_{l-})";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="lepMinusCosTheta";
      asymlabel="A_{P-}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.022476  ; stat_corr[0] =  0.031522  ; stat_uncorr[0] =  0.024238  ;
syst_corr[1] =  0.021190  ; stat_corr[1] =  0.031519  ; stat_uncorr[1] =  0.023234  ;
syst_corr[2] =  0.027232  ; stat_corr[2] =  0.036324  ; stat_uncorr[2] =  0.025650  ;
      break;
    }
      //   Top Polarization combining positively and negatively charged leptons
    case 4:
    {
      observablename="lep_costheta_cms";
      xaxislabel="cos(#theta_{l})";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="lepCosTheta";
      asymlabel="A_{P}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.6; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.6; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.024778  ; stat_corr[0] =  0.024972  ; stat_uncorr[0] =  0.017098  ;
syst_corr[1] =  0.023716  ; stat_corr[1] =  0.022656  ; stat_uncorr[1] =  0.016380  ;
syst_corr[2] =  0.028068  ; stat_corr[2] =  0.024181  ; stat_uncorr[2] =  0.018070  ;
      break;
    }
    //   Top Spin Correlation
    case 5:
    {
      observablename="top_spin_correlation";
      xaxislabel="cos(#theta_{l+})cos(#theta_{l-})";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="topSpinCorr";
      asymlabel="A_{c1c2}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.5; xbins2D[2]=-0.2; xbins2D[3]=0.0; xbins2D[4]=0.2; xbins2D[5]=0.5; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.029067  ; stat_corr[0] =  0.043529  ; stat_uncorr[0] =  0.034163  ;
syst_corr[1] =  0.034088  ; stat_corr[1] =  0.043614  ; stat_uncorr[1] =  0.034425  ;
syst_corr[2] =  0.034283  ; stat_corr[2] =  0.046582  ; stat_uncorr[2] =  0.036576  ;
      break;
    }
    //   Top Asy III
    case 6:
    {
      observablename="top_rapidtiydiff_Marco";
      //xaxislabel="|y_{top}|-|y_{tbar}|";
      xaxislabel="#Delta|y_{t}|";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="rapiditydiffMarco";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.7; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.7; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.011584  ; stat_corr[0] =  0.032123  ; stat_uncorr[0] =  0.024415  ;
syst_corr[1] =  0.007684  ; stat_corr[1] =  0.030558  ; stat_uncorr[1] =  0.023494  ;
syst_corr[2] =  0.010941  ; stat_corr[2] =  0.032998  ; stat_uncorr[2] =  0.024860  ;
      break;
    }
    //   Top Charge Asymmetry
    case 7:
    {
      observablename="top_costheta_cms";
      xaxislabel="cos(#theta_{top})";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="topCosTheta";
      asymlabel="A_{FB}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.7; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.7; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
syst_corr[0] =  0.016736  ; stat_corr[0] =  0.033656  ; stat_uncorr[0] =  0.024816  ;
syst_corr[1] =  0.010298  ; stat_corr[1] =  0.033133  ; stat_uncorr[1] =  0.023820  ;
syst_corr[2] =  0.013820  ; stat_corr[2] =  0.036253  ; stat_uncorr[2] =  0.025237  ;
      break;
    }
    //   Lepton Azimuthal Asymmetry
    case 8:
    {
      observablename="lep_azimuthal_asymmetry";
      xaxislabel="cos(#Delta#phi_{l+l-})";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="lepAzimAsym";
      asymlabel="A_{#Delta#phi}";
      xbins2D[0]=-1.0; xbins2D[1]=-0.8; xbins2D[2]=-0.4; xbins2D[3]=0.0; xbins2D[4]=0.4; xbins2D[5]=0.8; xbins2D[6]=1.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    //   Top Asy I
    case 9:
    {
      observablename="top_pseudorapidtiydiff_cms";
      xaxislabel="|#eta_{t}|-|#eta_{#bar{t}}|";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="pseudorapiditydiff";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-1.0; xbins2D[2]=-0.5; xbins2D[3]=0.0; xbins2D[4]=0.5; xbins2D[5]=1.0; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    //   Top Asy II
    case 10:
    {
      observablename="top_rapidtiydiff_cms";
      xaxislabel="(y_{top}-y_{#bar{t}})(y_{top}+y_{#bar{t}})";
      yaxislabel="|y_{t#bar{t}}|";
      acceptanceName="rapiditydiff";
      asymlabel="A_{C}";
      xbins2D[0]=-2.0; xbins2D[1]=-0.8; xbins2D[2]=-0.3; xbins2D[3]=0.0; xbins2D[4]=0.3; xbins2D[5]=0.8; xbins2D[6]=2.0;
      //ybins2D[0]=0.0; ybins2D[1]=0.3; ybins2D[2]=0.7; ybins2D[3]=1.5;
      ymin=ybins2D[0];
      ymax=ybins2D[3];
      xmin=xbins2D[0];
      xmax=xbins2D[6];
      break;
    }
    default:
    {
      cout<<"Set the variable switch";
    }
  }
}

void fillUnderOverFlow(TH1D *h1, float value, double weight, double Nsolns)
{
  double min = h1->GetXaxis()->GetXmin();
  double max = h1->GetXaxis()->GetXmax();

  if (value >= max) value = h1->GetBinCenter(h1->GetNbinsX());
  if (value <= min) value = h1->GetBinCenter(1);

  int bin_number = h1->FindBin(value);
  double orig_content = h1->GetBinContent(bin_number);
  double orig_error = h1->GetBinError(bin_number);

  //h1->Fill(value, weight);
  h1->SetBinContent( bin_number, orig_content+weight );
  h1->SetBinError( bin_number, sqrt( orig_error*orig_error + weight*weight*Nsolns ) );
}

//--------------------------------------------------------------------

void fillUnderOverFlow(TH2D *h2, float xvalue, float yvalue, double weight, double Nsolns)
{
  double maxx = h2->GetXaxis()->GetXmax();
  double minx = h2->GetXaxis()->GetXmin();
  double maxy = h2->GetYaxis()->GetXmax();
  double miny = h2->GetYaxis()->GetXmin();

  if (xvalue >= maxx) xvalue = h2->GetXaxis()->GetBinCenter(h2->GetNbinsX());
  if (xvalue <= minx) xvalue = h2->GetXaxis()->GetBinCenter(1);
  if (yvalue >= maxy) yvalue = h2->GetYaxis()->GetBinCenter(h2->GetNbinsY());
  if (yvalue <= miny) yvalue = h2->GetYaxis()->GetBinCenter(1);

  int bin_number = h2->FindBin(xvalue,yvalue);
  double orig_content = h2->GetBinContent(bin_number);
  double orig_error = h2->GetBinError(bin_number);

  //h2->Fill(xvalue, yvalue, weight);
  h2->SetBinContent( bin_number, orig_content+weight );
  h2->SetBinError( bin_number, sqrt( orig_error*orig_error + weight*weight*Nsolns ) );
}




//Given a TH2D and the x,y coordinates of a point, this function tells you what
//unwrapped bin that point would go into.
int getUnwrappedBin (TH2D *h2, double xval, double yval)
{
  int nx = h2->GetNbinsX();
  int ny = h2->GetNbinsY();
  int nxroot = nx+2;
  int nyroot = ny+2;

  int rootbin = h2->FindBin(xval, yval);

  //Deal with y-under/overflow, and corner cases
  if(rootbin < nxroot)  rootbin += nxroot;
  else if (rootbin >= (nyroot-1)*nxroot)  rootbin -= nxroot;

  //Deal with x-under/overflow
  if(rootbin%nxroot == 0) rootbin+=1;
  else if((rootbin+1)%nxroot == 0) rootbin -= 1;

  int unwrappedbin = rootbin - nx - 2*(rootbin/nxroot);

  if (unwrappedbin > nx*ny || unwrappedbin < 1) cout << "ERROR: unwrapped bin " << unwrappedbin << " doesn't exist! (ROOT bin " << rootbin << ")." << endl;
  return unwrappedbin;
}






// This is copied from the KIT group, with one important modification: to make a TH2 into a TH1,
// they concatenate columns, while we concatenate rows!
void unwrap2dhisto(TH2* h2, TH1* h1)
{
  int n=0;
  for(int y=1; y<=h2->GetNbinsY(); y++)
  {
	for(int x=1; x<=h2->GetNbinsX(); x++)
    {
	  n++;
	  h1->SetBinContent(n, h2->GetBinContent(x,y));
	  h1->SetBinError(n, h2->GetBinError(x,y));
	}
  }
  h1->Sumw2();
}


void rewrap1dhisto(TH1* h1, TH2* h2)
{
  int n=0;
  for(int y=1; y<=h2->GetNbinsY(); y++)
  {
	for(int x=1; x<=h2->GetNbinsX(); x++)
    {
	  n++;
	  h2->SetBinContent(x, y, h1->GetBinContent(n));
	  h2->SetBinError(x, y, h1->GetBinError(n));
	}
  }
  h1->Sumw2();

}


// The following is also copied from the KIT group code
double scaleBias = -99.9;
TUnfoldSys* myUnfold_TUnfoldGlobalPointerForTMinuit;
TH1D* myUnfold_hdataGlobalPointerForTMinuit;

void myUnfold_globalFunctionForMinuit(int &npar, double *gin, double &f, double *par, int iflag)
{
  const double logtau = par[0];
  const double scaleBias = par[1];
  myUnfold_TUnfoldGlobalPointerForTMinuit->DoUnfold(pow(10, logtau), myUnfold_hdataGlobalPointerForTMinuit, scaleBias);
  
  f = fabs(myUnfold_TUnfoldGlobalPointerForTMinuit->GetRhoAvg());
}



void minimizeRhoAverage(TUnfoldSys* unfold, TH1D* hdata, int nsteps, double log10min, double log10max)
{
  myUnfold_TUnfoldGlobalPointerForTMinuit = unfold;
  myUnfold_hdataGlobalPointerForTMinuit = hdata;
  
  // Instantiate Minuit for 2 parameters
  TMinuit minuit(2);
  minuit.SetFCN(myUnfold_globalFunctionForMinuit);
  minuit.SetPrintLevel(-1); // -1 no output, 1 output
  
  minuit.DefineParameter(0, "logtau", (log10min+log10max)/2, 1, log10min, log10max);
  minuit.DefineParameter(1, "scaleBias", scaleBias, 0, scaleBias, scaleBias);
  minuit.FixParameter(1);
  
  minuit.SetMaxIterations(100);
  minuit.Migrad();
  
  double bestlogtau = -1000;
  double bestlogtau_err = -1000; // error is meaningless because we don't have a likelihood, but method expects it
  minuit.GetParameter(0, bestlogtau, bestlogtau_err);
  unfold->DoUnfold(pow(10, bestlogtau), hdata, scaleBias); 
  
}
